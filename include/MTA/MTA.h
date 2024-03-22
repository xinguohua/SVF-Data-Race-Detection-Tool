/*
 * RaceDetector.h
 */

#ifndef MTA_H_
#define MTA_H_

#include <llvm/Pass.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/Instructions.h>
#include "llvm/Analysis/PostDominators.h"
#include "llvm/PassAnalysisSupport.h"
#include "Util/DataFlowUtil.h"

#include <set>
#include <utility>
#include <vector>

class PointerAnalysis;
class AndersenWaveDiff;
class ThreadCallGraph;
class MTAStat;
class TCT;
class MHP;
class LockAnalysis;
enum class Dependence {
    No,   // 完全无关
    programLogicBeforeDependence, /*程序逻辑顺序依赖 memory_order_relaxed*/
    programLogicAfterDependence, /*程序逻辑顺序依赖 memory_order_relaxed*/
    barrierOrderAcquireDependence, /*它防止后面的读或写操作被重排序到原子操作之前。*/
    barrierOrderReleaseDependence, /*之前的读或写操作被重排序到原子操作之后*/
    barrierOrderAcqRel, /*操作之前的写入对其他线程在该操作之后是可见的，同时操作之后的读取不能移到操作之前*/
    barrierOrderSeqRel, /*顺序一致*/
    ControlDependence,  //存在控制依赖
    DataDependence
};


enum class Result {
    No,   // 完全无关
    Program,
    Order,
};
/*!
 * Base data race detector
 */
class MTA: public llvm::ModulePass {

public:
    typedef std::set<const llvm::LoadInst*> LoadSet;
    typedef std::set<const llvm::StoreInst*> StoreSet;
    typedef std::map<const llvm::Function*, llvm::ScalarEvolution*> FunToSEMap;
    typedef std::map<const llvm::Function*, llvm::LoopInfo*> FunToLoopInfoMap;

    /// Pass ID
    static char ID;

    static llvm::ModulePass* modulePass;

    /// Constructor
    MTA();

    /// Destructor
    virtual ~MTA();


    /// We start the pass here
    virtual bool runOnModule(llvm::Module& module);
    /// Compute MHP
    virtual MHP* computeMHP(llvm::Module& module);
    /// Compute locksets
    virtual LockAnalysis* computeLocksets(TCT* tct);

    /// output test
    virtual void pairAnalysis(llvm::Module& module, MHP *mhp, LockAnalysis *lsa);

    const llvm::PostDominatorTree* getPostDT(const llvm::Function* fun);

    virtual Dependence isDependent(llvm::Instruction *A, std::__wrap_iter<std::vector<CallInst *,
            allocator < _Tp>>::const_pointer B);

    virtual Dependence findDependence(llvm::Instruction *A, llvm::Instruction *B, llvm::BasicBlock *A_Block, llvm::BasicBlock *B_Block);
        /// Pass name
    virtual llvm::StringRef getPassName() const {
        return "Multi threaded program analysis pass";
    }

    /// Get analysis usage
    inline virtual void getAnalysisUsage(llvm::AnalysisUsage& au) const {
        /// do not intend to change the IR in this pass,
        au.setPreservesAll();
        au.addRequired<llvm::ScalarEvolutionWrapperPass>();
    }

    // Get ScalarEvolution for Function F.
    static inline llvm::ScalarEvolution* getSE(const llvm::Function *F) {
        FunToSEMap::iterator it = func2ScevMap.find(F);
        if (it != func2ScevMap.end())
            return it->second;
        llvm::ScalarEvolutionWrapperPass *scev = &modulePass->getAnalysis<llvm::ScalarEvolutionWrapperPass>(*const_cast<llvm::Function*>(F));
        func2ScevMap[F] = &scev->getSE();
        return &scev->getSE();
    }

private:
    ThreadCallGraph* tcg;
    TCT* tct;
    MTAStat* stat;
    static FunToSEMap func2ScevMap;
    static FunToLoopInfoMap func2LoopInfoMap;

    PTACFInfoBuilder infoBuilder;		    ///< map a function to its loop info

};

class InstructionPair {
public:
    InstructionPair(llvm::Instruction* a, llvm::Instruction* b){
        inst1 = a;
        inst2 = b;
        alias = 0;
    }

    llvm::Instruction* getInst1() const{
        return inst1;
    }

    llvm::Instruction* getInst2() const{
        return inst2;
    }

    void setAlias(int result){
        alias = result;
    }

    int getAlias() const{
        return alias;
    }

    std::string getLoc1() const{
        return loc1;
    }

    std::string getLoc2() const{
        return loc2;
    }

    void setLoc1(std::string str) {
        loc1 = std::move(str);
    }

    void setLoc2(std::string str){
        loc2 = std::move(str);
    }

private:
    llvm::Instruction* inst1;
    llvm::Instruction* inst2;
    std::string loc1;
    std::string loc2;
    int alias;
};

#endif /* MTA_H_ */
