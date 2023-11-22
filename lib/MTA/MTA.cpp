/*
 * MTA.cpp
 *
 */

#include "MTA/MTA.h"
#include "MTA/MHP.h"
#include "MTA/TCT.h"
#include "MTA/LockAnalysis.h"
#include "MTA/MTAStat.h"
#include "WPA/Andersen.h"
#include "MTA/FSMPTA.h"
#include "Util/AnalysisUtil.h"

#include <llvm/Support/CommandLine.h>   // for llvm command line options
#include <llvm/IR/InstIterator.h>   // for inst iteration

#include <iostream>
#include <iomanip>
#include <fstream>
#include <regex>

using namespace llvm;
using namespace analysisUtil;


char MTA::ID = 0;
llvm::ModulePass* MTA::modulePass = NULL;
MTA::FunToSEMap MTA::func2ScevMap;
MTA::FunToLoopInfoMap MTA::func2LoopInfoMap;

MTA::MTA() :
    ModulePass(ID), tcg(NULL), tct(NULL) {
    stat = new MTAStat();
}

MTA::~MTA() {
    if (tcg)
        delete tcg;
}

/*!
 * Perform data race detection
 */
bool MTA::runOnModule(llvm::Module& module) {


    modulePass = this;

    MHP* mhp = computeMHP(module);
    LockAnalysis* lsa = computeLocksets(mhp->getTCT());
    pairAnalysis(module, mhp, lsa);

    delete mhp;
    delete lsa;

    return false;
}

/*!
 * Compute lock sets
 */
LockAnalysis* MTA::computeLocksets(TCT* tct) {
    LockAnalysis* lsa = new LockAnalysis(tct);
    lsa->analyze();
    return lsa;
}

MHP* MTA::computeMHP(llvm::Module& module) {

    DBOUT(DGENERAL, outs() << pasMsg("MTA analysis\n"));
    DBOUT(DMTA, outs() << pasMsg("MTA analysis\n"));
    PointerAnalysis* pta = AndersenWaveDiff::createAndersenWaveDiff(module);
    pta->getPTACallGraph()->dump("ptacg");
    DBOUT(DGENERAL, outs() << pasMsg("Create Thread Call Graph\n"));
    DBOUT(DMTA, outs() << pasMsg("Create Thread Call Graph\n"));
    tcg = new ThreadCallGraph(&module);
    tcg->updateCallGraph(pta);
    //tcg->updateJoinEdge(pta);
    DBOUT(DGENERAL, outs() << pasMsg("Build TCT\n"));
    DBOUT(DMTA, outs() << pasMsg("Build TCT\n"));

    DOTIMESTAT(double tctStart = stat->getClk());
    tct = new TCT(tcg, pta);
    DOTIMESTAT(double tctEnd = stat->getClk());
    DOTIMESTAT(stat->TCTTime += (tctEnd - tctStart) / TIMEINTERVAL);

    if (pta->printStat()) {
        stat->performThreadCallGraphStat(tcg);
        stat->performTCTStat(tct);
    }

    tcg->dump("tcg");

    DBOUT(DGENERAL, outs() << pasMsg("MHP analysis\n"));
    DBOUT(DMTA, outs() << pasMsg("MHP analysis\n"));

    DOTIMESTAT(double mhpStart = stat->getClk());
    MHP* mhp = new MHP(tct);
    mhp->analyze();
    DOTIMESTAT(double mhpEnd = stat->getClk());
    DOTIMESTAT(stat->MHPTime += (mhpEnd - mhpStart) / TIMEINTERVAL);

    DBOUT(DGENERAL, outs() << pasMsg("MHP analysis finish\n"));
    DBOUT(DMTA, outs() << pasMsg("MHP analysis finish\n"));
    return mhp;
}

bool hasDataRace(InstructionPair &pair, llvm::Module& module, MHP *mhp, LockAnalysis *lsa){
    //check alias
    PointerAnalysis* pta = AndersenWaveDiff::createAndersenWaveDiff(module);
    bool alias = false;
    if (const StoreInst *p1 = dyn_cast<StoreInst>(pair.getInst1())){
        if (const StoreInst *p2 = dyn_cast<StoreInst>(pair.getInst2())){
            AliasResult results = pta->alias(p1->getPointerOperand(),p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        } else if (const LoadInst *p2 = dyn_cast<LoadInst>(pair.getInst2())) {
            AliasResult results = pta->alias(p1->getPointerOperand(),p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        }
    } else if (const LoadInst *p1 = dyn_cast<LoadInst>(pair.getInst1())){
        if (const LoadInst *p2 = dyn_cast<LoadInst>(pair.getInst2())){
            AliasResult results = pta->alias(p1->getPointerOperand(),p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        } else if (const StoreInst *p2 = dyn_cast<StoreInst>(pair.getInst2())){
            AliasResult results = pta->alias(p1->getPointerOperand(),p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        }
    }
    if (!alias) return false;
    //check mhp
    if (!mhp->mayHappenInParallel(pair.getInst1(), pair.getInst2())) return false;
    //check lock
    return (!lsa->isProtectedByCommonLock(pair.getInst1(),pair.getInst2()));
}

bool isShared(const llvm::Value *val, llvm::Module& module){
    PointerAnalysis* pta = AndersenWaveDiff::createAndersenWaveDiff(module);
    PAG* pag = pta->getPAG();
    const PointsTo& target = pta->getPts(pag->getValueNode(val));
    for (PointsTo::iterator it = target.begin(), eit = target.end();
            it != eit; ++it) {
        const MemObj *obj = pag->getObject(*it);
        if (obj->isGlobalObj() || obj->isStaticObj() || obj->isHeap()){
            return true;
        }
    }
    return false;
}

bool isShared(const Instruction *loc, llvm::Module& module){
    if (const StoreInst *p1 = dyn_cast<StoreInst>(loc)){
        return isShared(p1->getPointerOperand(), module);
    } else if (const LoadInst *p1 = dyn_cast<LoadInst>(loc)){
        return isShared(p1->getPointerOperand(), module);
    }
    return false;
}


void MTA::pairAnalysis(llvm::Module& module, MHP *mhp, LockAnalysis *lsa){
    std::cout << " --- Running pair analysis ---\n";

    std::set<const Instruction *> instructions;
    std::vector<InstructionPair> pairs;

    for (Module::iterator F = module.begin(), E = module.end(); F != E; ++F) {
        for (inst_iterator II = inst_begin(&*F), E = inst_end(&*F); II != E; ++II) {
            const Instruction *inst = &*II;
            if (const StoreInst *st = dyn_cast<StoreInst>(inst)) {
                instructions.insert(st);
            }

            else if (const LoadInst *ld = dyn_cast<LoadInst>(inst)) {
                instructions.insert(ld);
            }
        }
    }
    int total = instructions.size();
    int count = 0;
    map<const Instruction *, std::string> instruction2LocMap;
    for (const auto &item: instructions){
        std::string s1;
        s1 = getSourceLoc(item);
        std::cout <<s1;
        instruction2LocMap[item] = s1;
    }
    // pair up all instructions (NC2) pairs and add to pair vector if they contain data race
    for (auto it = instructions.cbegin(); it != instructions.cend();){
        string first = instruction2LocMap[*it];
        std::cout << first;

                // if this instruction is not global/heap/static then skip
        ++count;
        if (count%50==0){
            std::cout << "Analysing... ";
            std::cout << int((double(count)/total)*100) << " %\r";    
            std::cout.flush();
        }

        if (!isShared(*it,module)) {
            ++it;
            continue;
        }
        for (auto it2 = std::next(it); it2 != instructions.cend(); ++it2){
            string two = instruction2LocMap[*it2];
            std::cout << two;

            InstructionPair pair = InstructionPair(*it,*it2);  
            if (hasDataRace(pair, module,mhp,lsa)){
                pairs.push_back(pair);
            }
        }
        ++it;
    }
    
    instructions.clear();

    // remove empty instructions
    // write to txt file
    std::ofstream outfile("/Users/xinguohua/Code/SVF-Data-Race-Detection-Tool/Release-build/bin/output.txt");

    if (!outfile.is_open()) {
        errs() << "Error opening file\n";
    }
    /*
    separate error message into
    line1
    filename1
    line2
    filename2
    for the plugin
    */
    std::string s1;
    std::string s2;
    std::regex line("ln: (\\d+)");
    std::regex file("fl: (.*)");
    std::smatch match;
    for (auto it = pairs.begin(); it != pairs.end(); ++it){
        s1 = getSourceLoc(it->getInst1());
        s2 = getSourceLoc(it->getInst2());
        it->setLoc1(s1);
        it->setLoc2(s2);

        if (s1.empty() || s2.empty()) continue;
        if (std::regex_search(s1, match, line))
            outfile << match[1] << std::endl;
        if (std::regex_search(s1, match, file))
            outfile << match[1] << std::endl;
        if (std::regex_search(s2, match, line))
            outfile << match[1] << std::endl;
        if (std::regex_search(s2, match, file))
            outfile << match[1] << std::endl;
    }
    outfile<<"==================="<<std::endl;
    for (auto it1 = pairs.begin(); it1 != std::prev(pairs.end()); ++it1) {
        for (auto it2 = std::next(it1); it2 != pairs.end(); ++it2) {
            auto element0 = *it1;
            auto element1 = *it2;
            // 两种交叉
            bool flag1 = isControlDependent(element0.getInst1(), element1.getInst1());
            bool flag2 = isControlDependent(element0.getInst2(), element1.getInst2());

            bool flag3= isControlDependent(element0.getInst1(), element1.getInst2());
            bool flag4 = isControlDependent(element0.getInst2(), element1.getInst1());
            if (!flag1 && flag2 || flag1 && !flag2 || !flag3 && flag4 || flag3 && !flag4){
                outfile<< "first race: " << element0.getLoc1()<<"---"<< element0.getLoc2()<< std::endl;
                outfile<< "second race: " << element1.getLoc1()<<"---"<< element1.getLoc2()<<std::endl;
            }
            if (!flag1 && flag2){
                outfile<< "Loc:" << element0.getLoc1()<<"---"<< element1.getLoc1()<<" dont dependency"<< std::endl;
                outfile<< "Loc:" << element0.getLoc2()<<"---"<< element1.getLoc2()<<" have dependency"<<std::endl;
                continue;
            }
            if (flag1 && !flag2){
                outfile<< "Loc:" << element0.getLoc1()<<"---"<< element1.getLoc1()<< " have dependency"<< std::endl;
                outfile<< "Loc:" << element0.getLoc2()<<"---"<< element1.getLoc2()<<" dont dependency"<<std::endl;
                continue;
            }
            if (!flag3 && flag4){
                outfile<< "Loc:" << element0.getLoc1()<<"---"<< element1.getLoc2()<< " dont dependency"<< std::endl;
                outfile<< "Loc:" << element0.getLoc2()<<"---"<< element1.getLoc1()<<" have dependency"<<std::endl;
                continue;
            }
            if (flag3 && !flag4){
                outfile<< "Loc:" << element0.getLoc1()<<"---"<< element1.getLoc2()<<" have dependency"<< std::endl;
                outfile<< "Loc:" << element0.getLoc2()<<"---"<< element1.getLoc1()<<" dont dependency"<<std::endl;
                continue;
            }
        }
    }


    outfile.flush();
    outfile.close();
    //need to also remove paairs that are a local variable. need to go into mem, and check.

}

bool MTA::isControlDependent(const llvm::Instruction* A,const  llvm::Instruction* B) {
    if (!A || !B) {
        return false;
    }

    // block
    if (!A->getParent() || !B->getParent()) {
        return false;
    }

    const BasicBlock * A_Block = A->getParent();
    const BasicBlock * B_Block = B->getParent();

    // Function
    if (!A->getParent()->getParent() || !B->getParent()->getParent()){
        return false;
    }

    // same Function
    if (A->getParent()->getParent() != B->getParent()->getParent()){
        return false;
    }

    // A is before B
    bool isA2B = std::find(pred_begin(B_Block), pred_end(B_Block), A_Block) != pred_end(B_Block);
    //B is before A
    bool isB2A = std::find(pred_begin(A_Block), pred_end(A_Block), B_Block) != pred_end(A_Block);

    if (!isA2B && !isB2A){
        return false;
    }

    const Function * F = A->getParent()->getParent();
    // 获取函数的后支配树
    const PostDominatorTree* pdt = getPostDT(F);
    if (isA2B){
        return !pdt->dominates(B_Block,A_Block);
    }

    if (isB2A){
        return !pdt->dominates(A_Block, B_Block);
    }
}

const llvm::PostDominatorTree* MTA::getPostDT(const llvm::Function* fun) {
    return infoBuilder.getPostDT(fun);
}
