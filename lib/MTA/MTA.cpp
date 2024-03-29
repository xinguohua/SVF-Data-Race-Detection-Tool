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
#include "Util/AnalysisUtil.h"
#include <llvm/IR/InstIterator.h>   // for inst iteration
#include <iostream>
#include <fstream>
#include <regex>
#include <queue>
#include <functional>
#include <unordered_set>
#include <unordered_map>

using namespace llvm;
using namespace analysisUtil;


char MTA::ID = 0;
llvm::ModulePass *MTA::modulePass = NULL;
MTA::FunToSEMap MTA::func2ScevMap;

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
bool MTA::runOnModule(llvm::Module &module) {
    clock_t start = clock();

    modulePass = this;

    MHP *mhp = computeMHP(module);
    LockAnalysis *lsa = computeLocksets(mhp->getTCT());
    pairAnalysis(module, mhp, lsa);

    clock_t end = clock();
    double time_spent = (double) (end - start) / CLOCKS_PER_SEC;
    printf("\nTime spent: %f seconds\n", time_spent);
    delete mhp;
    delete lsa;

    return false;
}

/*!
 * Compute lock sets
 */
LockAnalysis *MTA::computeLocksets(TCT *tct) {
    LockAnalysis *lsa = new LockAnalysis(tct);
    lsa->analyze();
    return lsa;
}

MHP *MTA::computeMHP(llvm::Module &module) {

    DBOUT(DGENERAL, outs() << pasMsg("MTA analysis\n"));
    DBOUT(DMTA, outs() << pasMsg("MTA analysis\n"));
    PointerAnalysis *pta = AndersenWaveDiff::createAndersenWaveDiff(module);
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
    MHP *mhp = new MHP(tct);
    mhp->analyze();
    DOTIMESTAT(double mhpEnd = stat->getClk());
    DOTIMESTAT(stat->MHPTime += (mhpEnd - mhpStart) / TIMEINTERVAL);

    DBOUT(DGENERAL, outs() << pasMsg("MHP analysis finish\n"));
    DBOUT(DMTA, outs() << pasMsg("MHP analysis finish\n"));
    return mhp;
}

bool hasDataRace(InstructionPair &pair, llvm::Module &module, MHP *mhp, LockAnalysis *lsa) {
    //check alias
    PointerAnalysis *pta = AndersenWaveDiff::createAndersenWaveDiff(module);
    bool alias = false;
    if (const StoreInst *p1 = dyn_cast<StoreInst>(pair.getInst1())) {
        if (const StoreInst *p2 = dyn_cast<StoreInst>(pair.getInst2())) {
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        } else if (const LoadInst *p2 = dyn_cast<LoadInst>(pair.getInst2())) {
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        }else if (const AtomicRMWInst *p2 = dyn_cast<AtomicRMWInst>(pair.getInst2())) {
            // If the second instruction is also an AtomicRMW, compare their pointer operands
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        }
    } else if (const LoadInst *p1 = dyn_cast<LoadInst>(pair.getInst1())) {
        if (const LoadInst *p2 = dyn_cast<LoadInst>(pair.getInst2())) {
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        } else if (const StoreInst *p2 = dyn_cast<StoreInst>(pair.getInst2())) {
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        }else if (const AtomicRMWInst *p2 = dyn_cast<AtomicRMWInst>(pair.getInst2())) {
            // If the second instruction is also an AtomicRMW, compare their pointer operands
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        } else if (const AtomicCmpXchgInst *p2 = dyn_cast<AtomicCmpXchgInst>(pair.getInst2())) {
            // For cmpxchg, we need to check both the address being compared and exchanged.
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            // The aliasing logic for cmpxchg is similar because it involves both reading and writing to the same memory location.
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        }
    } else if (const AtomicRMWInst *p1 = dyn_cast<AtomicRMWInst>(pair.getInst1())){
        // Handling AtomicRMW as the first instruction
        if (const LoadInst *p2 = dyn_cast<LoadInst>(pair.getInst2())) {
            // If the second instruction is a Load, compare their pointer operands
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        } else if (const StoreInst *p2 = dyn_cast<StoreInst>(pair.getInst2())) {
            // If the second instruction is a Store, compare their pointer operands
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        } else if (const AtomicRMWInst *p2 = dyn_cast<AtomicRMWInst>(pair.getInst2())) {
            // If the second instruction is also an AtomicRMW, compare their pointer operands
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        } else if (const AtomicCmpXchgInst *p2 = dyn_cast<AtomicCmpXchgInst>(pair.getInst2())) {
            // For cmpxchg, we need to check both the address being compared and exchanged.
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            // The aliasing logic for cmpxchg is similar because it involves both reading and writing to the same memory location.
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        }
    }else if (const AtomicCmpXchgInst *p1 = dyn_cast<AtomicCmpXchgInst>(pair.getInst1())){
        // Handling AtomicRMW as the first instruction
        if (const LoadInst *p2 = dyn_cast<LoadInst>(pair.getInst2())) {
            // If the second instruction is a Load, compare their pointer operands
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        } else if (const StoreInst *p2 = dyn_cast<StoreInst>(pair.getInst2())) {
            // If the second instruction is a Store, compare their pointer operands
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        } else if (const AtomicRMWInst *p2 = dyn_cast<AtomicRMWInst>(pair.getInst2())) {
            // If the second instruction is also an AtomicRMW, compare their pointer operands
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        } else if (const AtomicCmpXchgInst *p2 = dyn_cast<AtomicCmpXchgInst>(pair.getInst2())) {
            // For cmpxchg, we need to check both the address being compared and exchanged.
            AliasResult results = pta->alias(p1->getPointerOperand(), p2->getPointerOperand());
            pair.setAlias(results);
            // The aliasing logic for cmpxchg is similar because it involves both reading and writing to the same memory location.
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        }
    }else if (const CallInst *p1 = dyn_cast<CallInst>(pair.getInst1())){
        if (const CallInst *p2 = dyn_cast<CallInst>(pair.getInst2())) {
            AliasResult results;
            const Function *calledFunction = p1->getCalledFunction();
            const Function *calledFunction2 = p2->getCalledFunction();
            if (calledFunction && calledFunction2){
                StringRef name  = calledFunction->getName();
                StringRef name2  = calledFunction->getName();
                if ((name == "sem_wait" || name == "sem_post") && (name2 == "sem_wait" || name2 == "sem_post")) {
                    results = pta->alias(p1->getArgOperand(0), p2->getArgOperand(0));
                }
            }
            pair.setAlias(results);
            alias = (results == MayAlias || results == MustAlias || results == PartialAlias);
        }
    }
    if (!alias) return false;
    //check mhp
    if (!mhp->mayHappenInParallel(pair.getInst1(), pair.getInst2())) return false;
    //check lock
    return (!lsa->isProtectedByCommonLock(pair.getInst1(), pair.getInst2()));
}

bool isShared(const llvm::Value *val, llvm::Module &module) {
    PointerAnalysis *pta = AndersenWaveDiff::createAndersenWaveDiff(module);
    PAG *pag = pta->getPAG();
    const PointsTo &target = pta->getPts(pag->getValueNode(val));
    for (PointsTo::iterator it = target.begin(), eit = target.end();
         it != eit; ++it) {
        const MemObj *obj = pag->getObject(*it);
        if (obj->isGlobalObj() || obj->isStaticObj() || obj->isHeap() || obj->hasPtrObj()) {
            return true;
        }
    }
    return false;
}

bool isShared(const Instruction *loc, llvm::Module &module) {
    if (const StoreInst *p1 = dyn_cast<StoreInst>(loc)) {
        return isShared(p1->getPointerOperand(), module);
    }else if (const LoadInst *p1 = dyn_cast<LoadInst>(loc)) {
        return isShared(p1->getPointerOperand(), module);
    }else if (const AtomicRMWInst *p1 = dyn_cast<AtomicRMWInst>(loc)){
        return isShared(p1->getPointerOperand(), module);
    } else if (const AtomicCmpXchgInst *p1 = dyn_cast<AtomicCmpXchgInst>(loc)){
        return isShared(p1->getPointerOperand(), module);
    }else if (const CallInst *p1 = dyn_cast<CallInst>(loc)){
        return isShared(p1->getArgOperand(0), module);
    }
    return false;
}

Result dependencyRet(Dependence dependence) {
    if (dependence == Dependence::programLogicBeforeDependence ||
        dependence == Dependence::programLogicAfterDependence) {
        return Result::Program;
    }
    if (dependence == Dependence::No) {
        return Result::No;
    }
    return Result::Order;
}

// 定义哈希函数
struct InstructionPairHash {
    size_t operator()(const InstructionPair& pair) const {
        auto ptr1 = std::min(pair.getInst1(), pair.getInst2());
        auto ptr2 = std::max(pair.getInst1(), pair.getInst2());
        return std::hash<llvm::Instruction*>()(ptr1) ^ std::hash<llvm::Instruction*>()(ptr2);
    }
};

// 定义相等比较函数
struct InstructionPairEqual {
    bool operator()(const InstructionPair& lhs, const InstructionPair& rhs) const {
        return (lhs.getInst1() == rhs.getInst1() && lhs.getInst2() == rhs.getInst2()) ||
               (lhs.getInst1() == rhs.getInst2() && lhs.getInst2() == rhs.getInst1());
    }
};
std::string dependenceToString(Dependence dep) {
    switch (dep) {
        case Dependence::No:
            return "No";
        case Dependence::programLogicBeforeDependence:
            return "programLogicBeforeDependence";
        case Dependence::programLogicAfterDependence:
            return "programLogicAfterDependence";
        case Dependence::barrierOrderAcquireDependence:
            return "barrierOrderAcquireDependence";
        case Dependence::barrierOrderReleaseDependence:
            return "barrierOrderReleaseDependence";
        case Dependence::barrierOrderAcqRel:
            return "barrierOrderAcqRel";
        case Dependence::barrierOrderSeqRel:
            return "barrierOrderSeqRel";
        case Dependence::ControlDependence:
            return "ControlDependence";
        case Dependence::DataDependence:
            return "DataDependence";
        default:
            return "Unknown Dependence";
    }
}


void MTA::pairAnalysis(llvm::Module &module, MHP *mhp, LockAnalysis *lsa) {
    std::cout << " --- Running pair analysis ---\n";

    std::set<Instruction *> instructions;
    std::vector<InstructionPair> pairs;

    for (Module::iterator F = module.begin(), E = module.end(); F != E; ++F) {
        for (inst_iterator II = inst_begin(&*F), E = inst_end(&*F); II != E; ++II) {

            Instruction *inst = &*II;
            if (auto dbgLoc = inst->getDebugLoc()){
                unsigned line = dbgLoc.getLine();
                llvm::errs() << "Instruction at " <<  ":" << line<< "\n";
            }
            if (StoreInst *st = dyn_cast<StoreInst>(inst)) {
                instructions.insert(st);
            } else if (LoadInst *ld = dyn_cast<LoadInst>(inst)) {
                instructions.insert(ld);
            } else if (AtomicRMWInst *rmwInst = dyn_cast<AtomicRMWInst>(inst)){
                instructions.insert(rmwInst);
            } else if (AtomicCmpXchgInst *chgInst =  dyn_cast<AtomicCmpXchgInst>(inst)){
                instructions.insert(chgInst);
            }else if (CallInst *callInst = dyn_cast<CallInst>(inst)){
                if (const Function *calledFunction = callInst->getCalledFunction()) {
                    // 获取函数名称
                    StringRef functionName = calledFunction->getName();
                    if (functionName == "sem_wait" || functionName == "sem_post") {
                        instructions.insert(callInst);
                    }
                }
            }
        }
    }
    int total = instructions.size();
    int count = 0;
    map<const Instruction *, std::string> instruction2LocMap;
    for (const auto &item: instructions) {
        std::string s1;
        s1 = getSourceLoc(item);
        std::cout << s1;
        instruction2LocMap[item] = s1;
    }
    // pair up all instructions (NC2) pairs and add to pair vector if they contain data race
    for (auto it = instructions.cbegin(); it != instructions.cend();) {
        string first = instruction2LocMap[*it];
        std::cout << endl<<"first===" << first << endl;


        // if this instruction is not global/heap/static then skip
        ++count;
        if (count % 50 == 0) {
            std::cout << "Analysing... ";
            std::cout << int((double(count) / total) * 100) << " %\r";
            std::cout.flush();
        }

        if (!isShared(*it, module)) {
            ++it;
            continue;
        }
        for (auto it2 = std::next(it); it2 != instructions.cend(); ++it2) {
            string two = instruction2LocMap[*it2];
            std::cout << "two====" << two << endl;

            InstructionPair pair = InstructionPair(*it, *it2);
            if (hasDataRace(pair, module, mhp, lsa)) {
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
    for (auto it = pairs.begin(); it != pairs.end(); ++it) {
        s1 = getSourceLoc(it->getInst1());
        s2 = getSourceLoc(it->getInst2());
        it->setLoc1(s1);
        it->setLoc2(s2);
    }
    outfile << "===================" << std::endl;

    // 去重
    std::unordered_set<InstructionPair, InstructionPairHash, InstructionPairEqual> uniquePairs;
    for (const auto& pair : pairs) {
        uniquePairs.insert(pair);
    }
    for (const auto & uniquePair : uniquePairs) {
        if (uniquePair.getLoc1().empty() || uniquePair.getLoc2().empty()) continue;
        s1 = uniquePair.getLoc1();
        s2 = uniquePair.getLoc2();
        if (std::regex_search(s1, match, line))
            outfile << match[1] << ":";
        if (std::regex_search(s2, match, line))
            outfile << match[1] << std::endl;
        if (std::regex_search(s1, match, file))
            outfile << match[1] << ":";
        if (std::regex_search(s2, match, file))
            outfile << match[1] << std::endl;
        outfile << "pair======================" << std::endl;

        if (callOrder(uniquePair.getInst1(), uniquePair.getInst2(), module)){
            outfile << "single threat pair======================" << std::endl;

        }
    }


    for (auto it1 = uniquePairs.begin(); it1 != std::prev(uniquePairs.end()); ++it1) {
        for (auto it2 = std::next(it1); it2 != uniquePairs.end(); ++it2) {
            const auto& element0 = *it1;
            const auto& element1 = *it2;
            // 两种交叉
            Dependence flag1 = isDependent(element0.getInst1(), element1.getInst1());
            Dependence flag2 = isDependent(element0.getInst2(), element1.getInst2());
            Result result1 = dependencyRet(flag1);
            Result result2 = dependencyRet(flag2);

            Dependence flag3 = isDependent(element0.getInst1(), element1.getInst2());
            Dependence flag4 = isDependent(element0.getInst2(), element1.getInst1());
            Result result3 = dependencyRet(flag3);
            Result result4 = dependencyRet(flag4);

            if (element1.getLoc1().empty() && element1.getLoc2().empty()
                && element0.getLoc1().empty() && element0.getLoc2().empty()){
                continue;
            }


            if (result1 == Result::Program && result2 == Result::Order
                || result1 == Result::Order && result2 == Result::Program
                || result1 == Result::Program && result2 ==Result::Program
                || result3 == Result::Program && result4 == Result::Order
                || result3 == Result::Order && result4 == Result::Program
                || result3 == Result::Program && result4 == Result::Program) {
                outfile << "first race: " << element0.getLoc1() << "---" << element0.getLoc2() << std::endl;
                outfile << "second race: " << element1.getLoc1() << "---" << element1.getLoc2() << std::endl;
            }
            if (result1 == Result::Program && result2 == Result::Order) {
                outfile << "Loc:" << element0.getLoc1() << "---" << element1.getLoc1() << " dont dependency"
                        << std::endl;
                outfile << "Loc:" << element0.getLoc2() << "---" << element1.getLoc2() << " have dependency: "
                        << dependenceToString(flag2)<< std::endl;
                outfile << "================================" << std::endl;
                continue;
            }
            if (result1 == Result::Order && result2 == Result::Program) {
                outfile << "Loc:" << element0.getLoc1() << "---" << element1.getLoc1() << " have dependency: "
                        << dependenceToString(flag1) << std::endl;
                outfile << "Loc:" << element0.getLoc2() << "---" << element1.getLoc2() << " dont dependency"
                        << std::endl;
                outfile << "================================" << std::endl;
                continue;
            }
            if ( result1 == Result::Program && result2 ==Result::Program ){
                outfile << "Loc:" << element0.getLoc1() << "---" << element1.getLoc1() << " dont dependency"
                        << std::endl;
                outfile << "Loc:" << element0.getLoc2() << "---" << element1.getLoc2() << "dont dependency "
                        << std::endl;
                outfile << "================================" << std::endl;
            }
            if (result3 == Result::Program && result4 == Result::Order) {
                outfile << "Loc:" << element0.getLoc1() << "---" << element1.getLoc2() << " dont dependency"
                        << std::endl;
                outfile << "Loc:" << element0.getLoc2() << "---" << element1.getLoc1() << " have dependency: "
                        << dependenceToString(flag4)<< std::endl;
                outfile << "================================" << std::endl;
                continue;
            }
            if (result3 == Result::Order && result4 == Result::Program) {
                outfile << "Loc:" << element0.getLoc1() << "---" << element1.getLoc2() << " have dependency: "
                        << dependenceToString(flag3)<< std::endl;
                outfile << "Loc:" << element0.getLoc2() << "---" << element1.getLoc1() << " dont dependency"
                        << std::endl;
                outfile << "================================" << std::endl;
                continue;
            }
            if (result3 == Result::Program && result4 == Result::Program){
                outfile << "Loc:" << element0.getLoc1() << "---" << element1.getLoc2() << " dont dependency: "
                        << std::endl;
                outfile << "Loc:" << element0.getLoc2() << "---" << element1.getLoc1() << " dont dependency"
                        << std::endl;
                outfile << "================================" << std::endl;
            }
        }
    }


    outfile.flush();
    outfile.close();
    //need to also remove paairs that are a local variable. need to go into mem, and check.

}


const llvm::PostDominatorTree *MTA::getPostDT(const llvm::Function *fun) {
    return infoBuilder.getPostDT(fun);
}


void dfsFindPaths(llvm::BasicBlock *current, llvm::BasicBlock *end,
                  std::vector<llvm::BasicBlock *> &path,
                  std::vector<std::vector<llvm::BasicBlock *>> &paths,
                  std::set<llvm::BasicBlock *> &visited) {
    // 如果当前基本块已经访问过，避免循环，直接返回
    if (visited.find(current) != visited.end()) {
        return;
    }
    // 标记当前基本块为已访问
    visited.insert(current);
    // 将当前基本块加入到当前路径
    path.push_back(current);

    // 如果当前基本块是目标基本块，将当前路径添加到路径列表中
    if (current == end) {
        paths.push_back(path);
    } else {
        // 否则，继续DFS遍历
        for (llvm::succ_iterator it = llvm::succ_begin(current), et = llvm::succ_end(current); it != et; ++it) {
            dfsFindPaths(*it, end, path, paths, visited);
        }
    }

    // 回溯：移除当前基本块从路径和已访问集合，以便重用这些结构来探索不同的路径
    path.pop_back();
    visited.erase(current);
}


std::vector<std::vector<const llvm::Instruction *>>
collectInstructionsFromPaths(std::vector<std::vector<llvm::BasicBlock *>> paths,
                             const llvm::Instruction *A,
                             const llvm::Instruction *B) {
    std::vector<std::vector<const llvm::Instruction *>> allInstructions;

    for (const auto &path: paths) {
        std::vector<const llvm::Instruction *> pathInstructions;
        bool startCollecting = false;
        for (const auto *block: path) {
            for (const auto &instr: *block) {
                if (&instr == A || &instr == B) {
                    if (!startCollecting) {
                        startCollecting = true;
                        pathInstructions.push_back(&instr);
                        continue;
                    }
                    startCollecting = false;
                    pathInstructions.push_back(&instr);
                    break;
                }
                if (startCollecting) {
                    pathInstructions.push_back(&instr); // 收集指令
                }
            }
        }
        allInstructions.push_back(pathInstructions);
    }
    return allInstructions;
}

std::vector<std::vector<llvm::BasicBlock *>> findAllPaths(llvm::BasicBlock *start, llvm::BasicBlock *end) {
    std::vector<llvm::BasicBlock *> path;
    std::vector<std::vector<llvm::BasicBlock *>> paths;
    std::set<llvm::BasicBlock *> visited;

    dfsFindPaths(start, end, path, paths, visited);
    return paths;
}


std::vector<std::vector<const llvm::Instruction *>> traverseInstructions(llvm::Instruction *A, llvm::Instruction *B) {
    llvm::BasicBlock *A_Block = A->getParent();
    llvm::BasicBlock *B_Block = B->getParent();
    std::vector<const llvm::Instruction *> instructions;
    if (A_Block == B_Block) {
        bool startCollecting = false;
        for (const llvm::Instruction &instr: *A_Block) {
//            auto dbgLoc = &instr.getDebugLoc();  // 尝试获取调试位置信息
//            if (dbgLoc != nullptr){
//                llvm::errs() << "Instruction at "
//                             << dbgLoc->getLine() // 获取文件名
//                             << ":"
//                             << "\n";
//            }
            if (&instr == A || &instr == B) {
                if (!startCollecting) {
                    startCollecting = true;
                    instructions.push_back(&instr);
                    continue;
                }
                startCollecting = false;
                instructions.push_back(&instr);
                break;
            }
            if (startCollecting) {
                instructions.push_back(&instr); // 收集指令
            }
        }
        std::vector<std::vector<const llvm::Instruction *>> result;
        result.push_back(instructions);
        return result;
    } else {
        // 如果A和B在不同的基本块中，并且存在路径，则需要更复杂的逻辑来遍历这些基本块
        // 这里的实现依赖于具体的路径遍历策略
        std::vector<std::vector<llvm::BasicBlock *>> allBlock = findAllPaths(A_Block, B_Block);
        // 检查是否找到了路径
        if (!allBlock.empty()) {
            std::vector<std::vector<const llvm::Instruction *>> instructionsPaths = collectInstructionsFromPaths(
                    allBlock, A, B);
            return instructionsPaths;
        }
        std::vector<std::vector<llvm::BasicBlock *>> allBlock2 = findAllPaths(B_Block, A_Block);
        // 检查是否找到了路径
        if (!allBlock2.empty()) {
            std::vector<std::vector<const llvm::Instruction *>> instructionsPaths2 = collectInstructionsFromPaths(
                    allBlock2, A, B);
            return instructionsPaths2;
        }
        return std::vector<std::vector<const llvm::Instruction *>>{};
    }
}
std::map<Dependence, int> dependencyPriority = {
        {Dependence::DataDependence,  7},
        {Dependence::ControlDependence,  6},
        {Dependence::barrierOrderSeqRel, 5}, // 最高优先级
        {Dependence::barrierOrderAcqRel, 4},
        {Dependence::barrierOrderReleaseDependence, 3},
        {Dependence::barrierOrderAcquireDependence, 3},  // 最低优先级
        {Dependence::programLogicBeforeDependence, 2},
        {Dependence::programLogicAfterDependence, 2},
        {Dependence::No, 0},
};
//a Strong compare b
bool dependenceStrongCompare(Dependence a, Dependence b) {
    return dependencyPriority[a] > dependencyPriority[b];
}


using Path = std::vector<Instruction*>;

void dfsCheckFunctionCall(Function *current, Function *target, std::unordered_set<Function*> &visited, const Path& currentPath, std::vector<Path>& allPaths) {
    if (!target || visited.find(current) != visited.end()) {
        return;
    }
    visited.insert(current);

    for (auto it = inst_begin(current), eit = inst_end(current); it != eit; ++it) {
        if (auto *callInst = dyn_cast<CallInst>(&*it)) {
            Function *calledFunction = callInst->getCalledFunction();
            if (calledFunction) {
                // 复制当前路径并添加当前的调用指令
                Path newPath = currentPath;
                newPath.push_back(callInst);

                if (calledFunction == target) {
                    // 找到一条路径，保存它
                    allPaths.push_back(newPath);
                    // 注意：这里不返回，以探索其他可能的路径
                } else {
                    // 继续递归搜索
                    dfsCheckFunctionCall(calledFunction, target, visited, newPath, allPaths);
                }
            }
        }
    }
    // 从访问集合中移除当前函数，允许在不同路径中重新访问
    visited.erase(current);
}

// return atob
bool  findCallToFunction(Function *A, Function *B, std::vector<Path>& allPaths) {
    std::unordered_set<Function*> visited;
    Path currentPath;
    bool atob = false;

    dfsCheckFunctionCall(A, B, visited, currentPath, allPaths);
    if (!allPaths.empty()){
        atob = true;
    }
    if (!atob){
        allPaths.clear();
        dfsCheckFunctionCall(B, A, visited, currentPath, allPaths);
    }

    return atob;
}



Dependence MTA::isDependent(llvm::Instruction *A, llvm::Instruction *B) {
    if (!A || !B) {
        return Dependence::No;
    }

    if (A == B){
        return Dependence::No;
    }

    // block not null
    if (!A->getParent() || !B->getParent()) {
        return Dependence::No;
    }

    BasicBlock *A_Block = A->getParent();
    BasicBlock *B_Block = B->getParent();

    // Function not null
    if (!A->getParent()->getParent() || !B->getParent()->getParent()) {
        return Dependence::No;
    }

    // same Function
    if (A->getParent()->getParent() != B->getParent()->getParent()) {
        std::vector<Path> allPaths;
        bool atob = findCallToFunction(A->getParent()->getParent(), B->getParent()->getParent(), allPaths);
        if (allPaths.empty()) {
            return Dependence::No;
        }
        Dependence ret = Dependence::No;
        for (auto &path: allPaths){
            if (atob) {
                B = path.front();
                for (const auto &item: path){
                    Dependence temp = findDependence(A, B, A_Block, B->getParent());
                    if (dependenceStrongCompare(temp, ret)){
                        ret = temp;
                    }
                }
            } else{
                A = path.front();
                for (const auto &item: path){
                    Dependence temp = findDependence(A, B, A->getParent(), B_Block);
                    if (dependenceStrongCompare(temp, ret)){
                        ret = temp;
                    }
                }
            }
        }
        return ret;
    }
    return findDependence(A, B, A_Block, B_Block);
}



bool hasAcquireOrderingFromInstruction(const llvm::Function *function, llvm::Instruction *A) {
    bool startCheck = false;
    for (const auto &BB : *function) {
        for (const auto &Inst : BB) {
            if (&Inst == A) {
                startCheck = true;
            }
            if (startCheck) {
                // 检查这条指令是否具有acquire内存序
                llvm::AtomicOrdering ordering = llvm::AtomicOrdering::NotAtomic;
                if (auto *atomicLoad = dyn_cast<llvm::LoadInst>(&Inst)) {
                    if (atomicLoad->isAtomic()) {
                        ordering = atomicLoad->getOrdering();
                    }
                } else if (auto *atomicStore = dyn_cast<llvm::StoreInst>(&Inst)) {
                    if (atomicStore->isAtomic()) {
                        ordering = atomicStore->getOrdering();
                    }
                } else if (auto *atomicRMW = dyn_cast<llvm::AtomicRMWInst>(&Inst)) {
                    ordering = atomicRMW->getOrdering();
                } else if (auto *atomicCmpXchg = dyn_cast<llvm::AtomicCmpXchgInst>(&Inst)) {
                    ordering = atomicCmpXchg->getSuccessOrdering(); // 注意，cmpxchg有两个内存序，这里仅检查成功的情况
                }

                if (ordering == llvm::AtomicOrdering::Acquire || ordering == llvm::AtomicOrdering::AcquireRelease || ordering == llvm::AtomicOrdering::SequentiallyConsistent) {
                    return true; // 找到具有acquire内存序的指令
                }
            }
        }
    }
    return false; // 未找到
}


bool hasReleaseOrderingFromInstruction(const Function *function, Instruction *A) {
    bool startCheck = true;
    for (const auto &BB : *function) {
        for (const auto &Inst : BB) {
            if (&Inst == A) {
                startCheck = false;
            }
            if (startCheck) {
                // 检查这条指令是否具有release内存序
                AtomicOrdering ordering = AtomicOrdering::NotAtomic;
                if (auto *atomicLoad = dyn_cast<LoadInst>(&Inst)) {
                    ordering = atomicLoad->getOrdering();
                } else if (auto *atomicStore = dyn_cast<StoreInst>(&Inst)) {
                    if (atomicStore->isAtomic()) {
                        ordering = atomicStore->getOrdering();
                    }
                } else if (auto *atomicRMW = dyn_cast<AtomicRMWInst>(&Inst)) {
                    ordering = atomicRMW->getOrdering();
                } else if (auto *atomicCmpXchg = dyn_cast<AtomicCmpXchgInst>(&Inst)) {
                    ordering = atomicCmpXchg->getSuccessOrdering(); // 注意，cmpxchg有两个内存序，这里仅检查成功的情况
                }

                if (ordering == AtomicOrdering::Release || ordering == AtomicOrdering::AcquireRelease) {
                    return true; // 找到具有release内存序的指令
                }
            } else{
                break;
            }
        }
    }
    return false; // 未找到
}


void reverseTraverse(const PTACallGraphNode* startNode,
                     std::vector<const PTACallGraphNode*>& visited,
                     std::vector<const PTACallGraphNode*>& path,
                     std::vector<std::vector<const PTACallGraphNode*>>& allPaths) {
    // 如果这个节点已经访问过，则返回
    if (std::find(visited.begin(), visited.end(), startNode) != visited.end()) {
        return;
    }

    // 标记当前节点为已访问
    visited.push_back(startNode);
    // 将当前节点加入到路径中
    path.push_back(startNode);

    // 如果当前节点是程序入口，则将这条路径加入到所有路径中
    if (analysisUtil::isProgEntryFunction(startNode->getFunction())) {
        allPaths.push_back(std::vector<const PTACallGraphNode*>(path));
    } else {
        // 否则，继续反向遍历入边
        for (auto it = startNode->InEdgeBegin(), eit = startNode->InEdgeEnd(); it != eit; ++it) {
            PTACallGraphEdge* edge = *it;
            reverseTraverse(edge->getSrcNode(), visited, path, allPaths);
        }
    }
    // 在返回前，将当前节点从路径中移除，以便回溯
    path.pop_back();
}


std::set<const PTACallGraphNode*> FindCommonNodes(
        const std::vector<std::vector<const PTACallGraphNode*>>& allPathsA,
        const std::vector<std::vector<const PTACallGraphNode*>>& allPathsB) {

    std::set<const PTACallGraphNode*> flatSetA, flatSetB;

    // 展平 allPathsA 到 flatSetA
    for (const auto& path : allPathsA) {
        for (const auto& node : path) {
            flatSetA.insert(node);
        }
    }

    // 展平 allPathsB 到 flatSetB
    for (const auto& path : allPathsB) {
        for (const auto& node : path) {
            flatSetB.insert(node);
        }
    }

    // 寻找交集
    std::set<const PTACallGraphNode*> commonNodes;
    std::set_intersection(flatSetA.begin(), flatSetA.end(),
                          flatSetB.begin(), flatSetB.end(),
                          std::inserter(commonNodes, commonNodes.begin()));

    return commonNodes;
}

using Path1 = std::vector<const PTACallGraphNode*>;
using NodeToPathMap = std::unordered_map<const PTACallGraphNode*, Path1>;
const PTACallGraphNode* findFirstCommonAncestorAndRecordPath(
        const std::vector<Path1>& allPathsA,
        const std::vector<Path1>& allPathsB,
        Path1& pathFromCommonToA,
        Path1& pathFromCommonToB) {

    NodeToPathMap nodeToPathMapA;
    std::unordered_set<const PTACallGraphNode*> pathNodesA;

    // 构建 A 的节点集合，记录路径
    for (const auto& path : allPathsA) {
        for (const auto& node : path) {
            nodeToPathMapA[node] = path; // 直接关联节点到完整路径
            pathNodesA.insert(node);
        }
    }

    // 遍历 B 的路径，寻找公共祖先并记录路径映射
    for (const auto& path : allPathsB) {
        for (const auto& node : path) {
            if (pathNodesA.find(node) != pathNodesA.end()) {
                // 找到第一个公共祖先
                auto itA = std::find(nodeToPathMapA[node].begin(), nodeToPathMapA[node].end(), node);
                if (itA != nodeToPathMapA[node].end()) {
                    // 截取从公共祖先到A的路径
                    pathFromCommonToA.assign(nodeToPathMapA[node].begin(), itA+1);
                    std::reverse(pathFromCommonToA.begin(), pathFromCommonToA.end());
                }

                auto itB = std::find(path.begin(), path.end(), node);
                if (itB != path.end()) {
                    // 截取从公共祖先到B的路径
                    pathFromCommonToB.assign(path.begin(), itB+1);
                    std::reverse(pathFromCommonToB.begin(), pathFromCommonToB.end());
                }
                return node; // 返回第一个公共祖先节点
            }
        }
    }

    return nullptr; // 如果没有找到公共节点，则返回nullptr
}


CallInst* findPthreadCreateCall(Function *caller, Function *target) {
    for (auto &BB : *caller) {
        for (auto &I : BB) {
            if (auto *callInst = dyn_cast<CallInst>(&I)) {
                if (Function *calledFunction = callInst->getCalledFunction()) {
                    if (calledFunction->getName() == "pthread_create") {
                        Value *thirdArg = callInst->getArgOperand(2);
                        if (auto *func = dyn_cast<Function>(thirdArg->stripPointerCasts())) {
                            if (func == target) {
                                // Found the target function being passed to pthread_create
                                // Return the call instruction
                                return callInst;
                            }
                        }
                    }
                }
            }
        }
    }
    return nullptr; // If no call to pthread_create with the target function is found
}


bool MTA::callOrder(llvm::Instruction *A, llvm::Instruction *B, llvm::Module& module){
    PointerAnalysis *pta = AndersenWaveDiff::createAndersenWaveDiff(module);
    PAG *pag = pta->getPAG();
    if (!A || !B) {
        return false;
    }

    if (A == B){
        return false;
    }

    // block not null
    if (!A->getParent() || !B->getParent()) {
        return false;
    }

     BasicBlock *A_Block = A->getParent();
     BasicBlock *B_Block = B->getParent();

    // Function not null
    if (!A->getParent()->getParent() || !B->getParent()->getParent()) {
        return false;
    }

    llvm::Instruction* insA;
    llvm::Instruction* insB;
    if (A->getParent()->getParent() != B->getParent()->getParent()){
        PTACallGraphNode* AFunctionNode = pta-> getPTACallGraph()-> getCallGraphNode(A->getParent()->getParent());
        PTACallGraphNode* BFunctionNode = pta-> getPTACallGraph()->getCallGraphNode(B->getParent()->getParent());

        std::vector<std::vector<const PTACallGraphNode*>> AallPaths;
        std::vector<const PTACallGraphNode*> Avisited, Apath;
        reverseTraverse(AFunctionNode, Avisited, Apath, AallPaths);

        std::vector<std::vector<const PTACallGraphNode*>> BallPaths;
        std::vector<const PTACallGraphNode*> Bvisited, Bpath;
        reverseTraverse(BFunctionNode, Bvisited, Bpath, BallPaths);

        Path1 pathFromCommonToA, pathFromCommonToB;

        // 调用函数
        const PTACallGraphNode* commonAncestor = findFirstCommonAncestorAndRecordPath(AallPaths, BallPaths, pathFromCommonToA, pathFromCommonToB);
        if (commonAncestor == nullptr){
            return false;
        }

        PTACallGraphNode* src = const_cast<PTACallGraphNode *>(pathFromCommonToA[0]);
        PTACallGraphNode* dst = const_cast<PTACallGraphNode *>(pathFromCommonToA[1]);
        if (src == nullptr && dst == nullptr || src == nullptr) return false;
        if (dst == nullptr){
            insA = A;
        } else{
            PTACallGraphEdge* edge = pta-> getPTACallGraph()->hasGraphEdge(src, dst, PTACallGraphEdge::CallRetEdge);
            if (edge == nullptr){
                CallInst* callInst = findPthreadCreateCall((Function *)src->getFunction(), (Function *)dst->getFunction());
                if (callInst){
                    insA = callInst;
                } else{
                    return false;
                }
            } else{
                insA = (llvm::Instruction*)*edge->getDirectCalls().begin();
            }
        }
        PTACallGraphNode* src1 = const_cast<PTACallGraphNode *>(pathFromCommonToB[0]);
        PTACallGraphNode*  dst1= const_cast<PTACallGraphNode *>(pathFromCommonToB[1]);
        if (dst1 == nullptr){
            insB =B;
        } else{
            PTACallGraphEdge* edge1 = pta-> getPTACallGraph()->hasGraphEdge(src1, dst1, PTACallGraphEdge::CallRetEdge);
            if (edge1 == nullptr){
                CallInst* callInst = findPthreadCreateCall((Function *)src1->getFunction(), (Function *)dst1->getFunction());
                if (callInst){
                    insB = callInst;
                } else{
                    return false;
                }
            } else{
                insB = (llvm::Instruction*)*edge1->getDirectCalls().begin();
            }
        }
    } else{
        insA = A;
        insB = B;
    };
    std::vector<std::vector<const llvm::Instruction *>> allPathInstruction = traverseInstructions(insA, insB);


    if (allPathInstruction.empty()){
        return false;
    }

    if (allPathInstruction.front().front() == insA){
        if (!(hasAcquireOrderingFromInstruction(A->getParent()->getParent(), A) && hasReleaseOrderingFromInstruction(B->getParent()->getParent(), B))){
            return true;
        }
    } else if (allPathInstruction.front().front() == insB){
        if (!(hasAcquireOrderingFromInstruction(B->getParent()->getParent(), B) && hasReleaseOrderingFromInstruction(A->getParent()->getParent(), A))){
            return true;
        }
    }
    return false;
}





Dependence MTA::findDependence(llvm::Instruction *A, llvm::Instruction *B, llvm::BasicBlock* A_Block, llvm::BasicBlock* B_Block) {

    //================控制依赖===================
    // A is before B
    bool isA2B = std::find(pred_begin(B_Block), pred_end(B_Block), A_Block) != pred_end(B_Block);
    //B is before A
    bool isB2A = std::find(pred_begin(A_Block), pred_end(A_Block), B_Block) != pred_end(A_Block);

    if (isA2B || isB2A) {
        const Function *F = A->getParent()->getParent();
        // 获取函数的后支配树
        const PostDominatorTree *pdt = getPostDT(F);
        if (isA2B) {
            if (!pdt->dominates(B_Block, A_Block)) {
                return Dependence::ControlDependence;
            }
        }

        if (isB2A) {
            if (!pdt->dominates(A_Block, B_Block)) {
                return Dependence::ControlDependence;
            }
        }
    }
    //==================================================
//    programLogicBeforeDependence, /*程序逻辑顺序依赖 memory_order_relaxed*/
//            programLogicAfterDependence, /*程序逻辑顺序依赖 memory_order_relaxed*/
//            barrierOrderAcquireDependence, /*它防止后面的读或写操作被重排序到原子操作之前。*/
//            barrierOrderReleaseDependence, /*之前的读或写操作被重排序到原子操作之后*/
//            barrierOrderAcqRel, /*操作之前的写入对其他线程在该操作之后是可见的，同时操作之后的读取不能移到操作之前*/
//            barrierOrderSeqRel, /*顺序一致*/
//            ControlDependence,  //存在控制依赖
//            DataDependence
    std::vector<std::vector<const llvm::Instruction *>> allPathInstruction = traverseInstructions(A, B);
    if (allPathInstruction.empty()) {
        return Dependence::No;
    }
    // =========== 每条路径屏障
    std::vector<bool> acquireFlag(allPathInstruction.size(), false);
    std::vector<bool> releaseFlag(allPathInstruction.size(), false);
    std::vector<bool> acqRelFlag(allPathInstruction.size(), false);
    std::vector<bool> seqFlag(allPathInstruction.size(), false);

    bool aFirst = false;
    bool begin = true;
    Dependence allPathResult;
    for (size_t i = 0; i < allPathInstruction.size(); ++i) {
        for (const auto *instr: allPathInstruction[i]) {
            if (A == instr && begin) {
                aFirst = true;
                begin = false;
            }
            llvm::AtomicOrdering ordering = llvm::AtomicOrdering::NotAtomic;

            // 根据指令类型获取内存排序语义
            if (const auto *atomicInst = llvm::dyn_cast<llvm::AtomicRMWInst>(instr)) {
                ordering = atomicInst->getOrdering();
            } else if (const auto *cmpxchgInst = llvm::dyn_cast<llvm::AtomicCmpXchgInst>(instr)) {
                ordering = cmpxchgInst->getSuccessOrdering(); // 注意：cmpxchg还有失败时的排序
            } else if (const auto *fenceInst = llvm::dyn_cast<llvm::FenceInst>(instr)) {
                ordering = fenceInst->getOrdering();
            }

            // 根据内存排序设置标志
            switch (ordering) {
                case llvm::AtomicOrdering::Acquire:
                    acquireFlag[i] = true;
                    break;
                case llvm::AtomicOrdering::Release:
                    releaseFlag[i] = true;
                    break;
                case llvm::AtomicOrdering::AcquireRelease:
                    acqRelFlag[i] = true;
                    break;
                case llvm::AtomicOrdering::SequentiallyConsistent:
                    seqFlag[i] = true;
                    break;
                default:
                    // 其他内存排序类型不做处理
                    break;
            }
        }
    }

    //=============ProgramOrder
    if (aFirst) {
        allPathResult = Dependence::programLogicBeforeDependence;
    } else{
        allPathResult = Dependence::programLogicAfterDependence;
    }

    for (size_t i = 0; i < allPathInstruction.size(); ++i) {
        Dependence thisPathResult = Dependence::No;
        if (seqFlag[i]){
            thisPathResult = Dependence::barrierOrderSeqRel;
        }else if (acqRelFlag[i] || acquireFlag[i] && releaseFlag[i]){
            thisPathResult =  Dependence::barrierOrderAcqRel;
        }else if (acquireFlag[i]) {
            thisPathResult = Dependence::barrierOrderAcquireDependence;
        }else if (releaseFlag[i]){
            thisPathResult = Dependence::barrierOrderReleaseDependence;
        }
        if (dependenceStrongCompare(thisPathResult, allPathResult)){
            allPathResult = thisPathResult;
        }
    }
    //===========Data
    return allPathResult;
}

