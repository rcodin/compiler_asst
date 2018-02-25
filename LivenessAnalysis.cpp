#define DEBUG_TYPE "opCounter"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

#include <cstdio>
#include <iostream>
#include <vector>
#include <map>
#include <sstream>
#include <string>
#include <iomanip>


using namespace llvm;

namespace {
	typedef std::vector<BitVector> BitVectorList;
    typedef std::vector<BasicBlock*> BasicBlockList;
    typedef std::vector<Instruction*> InstructionList;
struct LivenessAnalysis : public FunctionPass {
	static char ID;
	LivenessAnalysis() : FunctionPass(ID) {}
	std::map<std::string, int> opCounter;
	std::map<BasicBlock*, BasicBlockList > blockPreds;
	std::map<BasicBlock*, BasicBlockList > blockSuccs;
	std::map<BasicBlock*, int> blockToInt;//working set vector for representing working set
	BitVector workingVector;

	bool runOnFunction(Function &F) override {
		std::vector<Instruction*> instructionList;
		std::vector<Instruction*>::iterator it;
		it = instructionList.begin();
		for (Function::iterator BB = F.begin(), EB = F.end(); BB != EB; BB++) {
			for (BasicBlock::iterator inst = BB->begin(), ei = BB->end(); inst != ei; ++inst) {
				it = instructionList.end();
				it = instructionList.insert(it, &(*inst));
			}
		}
		// errs()<<"Number of instruction is : "<<instructionList.size()<<"\n";
		std::map<Instruction*, std::set<std::string>> liveVariables;

		std::map<Instruction*, std::set<std::string>> startLiveVars;
		bool modify = true;
		while (modify) {
			modify = false;
			for (std::vector<Instruction*>::iterator inst = instructionList.begin(), ei = instructionList.end(); inst != ei; ++inst) {
				// errs()<<*(*inst)<<"\n";
				if ((*inst)->isTerminator()) {
					// errs()<<*(*inst)<<"\n";
					BasicBlock* block = (*inst)->getParent();
					std::set<std::string> outSet;
					
					for (succ_iterator neighbour = succ_begin(block), last = succ_end(block); neighbour != last; ++neighbour) {
						BasicBlock* neighbourBlock = *neighbour;
						Instruction* firstInst = (Instruction *)neighbourBlock->begin();
						std::set<std::string> liveVarSet = liveVariables[firstInst];
						outSet.insert(liveVarSet.begin(),liveVarSet.end());
					}
					startLiveVars[*inst].insert(outSet.begin(), outSet.end()); 
					if (auto* brInst = dyn_cast<BranchInst>(*inst)) {
						// BranchInst brInst = cast<BranchInst>(**inst);

						if (brInst->isConditional()) {
							std::string condVar = brInst->getCondition()->getName();
							if (condVar.compare(""))
								outSet.insert(condVar);
						}
					}
					else if (auto* retInst = dyn_cast<ReturnInst>(*inst)) {
						std::string retValStr = retInst->getReturnValue()->getName();

						if (retValStr.compare(""))
							outSet.insert(retValStr);
					}
					if (liveVariables[*inst] != outSet) {
						modify = true;
					}
					liveVariables[*inst].insert(outSet.begin(), outSet.end()); 
					if (liveVariables[*inst] != outSet) {
						modify = true;
					}
					liveVariables[*inst].insert(outSet.begin(), outSet.end());
				}
				else {
					std::vector<Instruction*>::iterator prevIt = inst + 1;
					std::set<std::string> prevLiveVars;
					prevLiveVars.insert(liveVariables[*prevIt].begin(), liveVariables[*prevIt].end());
					if (PHINode* phi_insn = dyn_cast<PHINode>(*inst)) {
						// errs()<<(**inst)<<" Name : "<<(**inst).getName()<<" phi value : ";

						for (std::set<std::string>::iterator liveIt = prevLiveVars.begin(),
							endLiveIt = prevLiveVars.end(); liveIt != endLiveIt; liveIt++) {
							std::string str = *liveIt;
							
							std::string defName = (*inst)->getName();							
							if (str.compare(defName) == 0) {
								prevLiveVars.erase(str);
							}
						}
                        for (int ind = 0; ind < phi_insn->getNumIncomingValues(); ind++) {

                            Value* val = phi_insn->getIncomingValue(ind);
                            if (isa<Instruction>(val) || isa<Argument>(val)) {
                            	// errs()<<val->getName()<<" ";
                            	prevLiveVars.insert(val->getName());
                            }
                        }
                        // errs()<<"\n";
                    }
					else if (isa<StoreInst>(**inst)) {
						std::string useName = (*inst)->getOperand(0)->getName();
						std::string defName = (*inst)->getOperand(1)->getName();

						for (std::set<std::string>::iterator liveIt = prevLiveVars.begin(),
							endLiveIt = prevLiveVars.end(); liveIt != endLiveIt; liveIt++) {
							std::string str = *liveIt;
							if (str.compare(defName) == 0) {
								prevLiveVars.erase(str);
							}
						}
						if (useName.compare("")) {
							// errs()<<useName<<"\n";
							prevLiveVars.insert(useName);	
						}
					}
					else if (isa<AllocaInst>(**inst)) {

					}
					else if (isa<GetElementPtrInst>(** inst)) {
						// errs()<<(**inst);
						// errs()<<" getemementptr instruction of found"<<"\n";
						std::string useName = (*inst)->getOperand(0)->getName();
						std::string defName = (*inst)->getName();

						for (std::set<std::string>::iterator liveIt = prevLiveVars.begin(),
							endLiveIt = prevLiveVars.end(); liveIt != endLiveIt; liveIt++) {
							std::string str = *liveIt;
							if (str.compare(defName) == 0) {
								prevLiveVars.erase(str);
							}
						}
						// errs()<<useName<<"\n";
						if (useName.compare(""))
							prevLiveVars.insert(useName);
					}
					else {
						std::string defName = (*inst)->getName();

						for (std::set<std::string>::iterator liveIt = prevLiveVars.begin(),
							endLiveIt = prevLiveVars.end(); liveIt != endLiveIt; liveIt++) {
							std::string str = *liveIt;

							if (str.compare(defName) == 0) {
								prevLiveVars.erase(str);
							}
						}
						for(User::op_iterator opIt = (*inst)->op_begin(), opEnd = (*inst)->op_end();
								opIt!=opEnd; ++opIt) {
							Value *opnd = *opIt;
							std::string useElems (opnd->getName());
							if (!useElems.compare("")) {
								continue;
							}
							if (isa<GlobalValue>(opnd)) {
								// errs()<<"Global value found : "<< opnd->getName()<<"\n";
								continue;
							}
							// errs()<<useElems<<"\n";
							prevLiveVars.insert(useElems);
						}
					}
					std::string defElem ((*inst)->getName()); //this is the def in current element
					Value* val = *inst;
					// errs()<<"Instruction is : "<<*val<<"\n";
					for(User::op_iterator opIt = (*inst)->op_begin(), opEnd = (*inst)->op_end();
								opIt!=opEnd; ++opIt) {
					}

					if (liveVariables[*inst] != prevLiveVars) {
						modify = true;
					}
					liveVariables[*inst].insert(prevLiveVars.begin(), prevLiveVars.end()); 
				}
			}
		}
		int histogram[100] = {0};
		int max = 0;
		for (Function::iterator BB = F.begin(), EB = F.end(); BB != EB; BB++) {
			errs()<<"------------------------------BB enrty-----------------------------"<<"\n";
			for (BasicBlock::iterator inst = BB->begin(), ei = BB->end(); inst != ei; ++inst) {
				// it = instructionList.insert(it, &(*inst));
				errs()<<"{";
				std::set<std::string> instLiveVars = liveVariables[&(*inst)];
				int inPerInstSize = instLiveVars.size();
				if (max < inPerInstSize)
					max = inPerInstSize;
				histogram[inPerInstSize]++;
				for (std::set<std::string>::iterator liveIt = instLiveVars.begin(), endIt = instLiveVars.end();
								liveIt != endIt; liveIt++) {
					// liveIt++;
					// if ((liveIt) == endIt) {
					// 	liveIt--;
					// 	errs()<<*liveIt;
					// 	break;
					// }
					// else {
					// 	liveIt--;
					// 	liveIt--;
						errs()<<*liveIt<<", ";
					// }
				}
				errs()<<"}\n"<<*inst<<"\n";
				if ((inst)->isTerminator()) {
					int outPerBlockSize = startLiveVars[&(*inst)].size();
					if (max < outPerBlockSize)
						max = outPerBlockSize;
					histogram[outPerBlockSize]++;
					errs()<<"{";
					for (std::set<std::string>::iterator liveIt = startLiveVars[&(*inst)].begin(),
									endIt = startLiveVars[&(*inst)].end(); liveIt != endIt; liveIt++) {
						errs()<<*liveIt<<", ";
					}
					errs()<<"}\n";
				}
			}
			errs()<<"------------------------------BB exit------------------------------"<<"\n";
		}
		errs()<<"\n\n\t"<<"histogram"<<"\n";
		for (int i = 0; i <= max ; i++)
			errs()<<i<<"\t\t\t"<<histogram[i]<<"\n";
		opCounter.clear();
		return false;
	}
	void getInSet() {

	}
 // end of struct Hello
};  // end of anonymous namespace
}

char LivenessAnalysis::ID = 0;
static RegisterPass<LivenessAnalysis> X("liveness", "Liveness Analysis Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);