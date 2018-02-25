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
	struct UnInitAnalysis : public FunctionPass {
		static char ID;
		UnInitAnalysis() : FunctionPass(ID) {}
		std::map<std::string, int> opCounter;
		
		bool runOnFunction(Function &F) override {
			

			std::vector<Instruction*> instructionList;
			std::vector<Instruction*>::iterator it;
			std::set<Instruction*> firstBlockInsts; //The first instruction of the blocks
			std::set<std::string> universeVar;
			it = instructionList.begin();
			for (Function::iterator BB = F.begin(), EB = F.end(); BB != EB; BB++) {
				firstBlockInsts.insert(&(*BB->begin()));
				for (BasicBlock::iterator inst = BB->begin(), ei = BB->end(); inst != ei; ++inst) {
					it = instructionList.end();
					it = instructionList.insert(it, &(*inst));
					for(User::op_iterator opIt = (inst)->op_begin(), opEnd = (inst)->op_end();
								opIt!=opEnd; ++opIt) {
						Value *opnd = *opIt;
						
						if (isa<AllocaInst>(opnd)||isa<BranchInst>(opnd)||isa<BranchInst>(opnd)) {
							continue;
						}
						std::string defName (opnd->getName());
						if (isa<StoreInst>(*inst)) {
							defName = (inst)->getOperand(1)->getName();
						}
						if ((!defName.compare(""))||(!defName.compare(" "))||(!defName.compare("\t"))) {
							continue;
						}
						if (isa<GlobalValue>(opnd)) {
							continue;
						}
						if (auto* brInst = dyn_cast<BranchInst>(inst)) {
						// BranchInst brInst = cast<BranchInst>(**inst);

							if (brInst->isConditional()) {
								universeVar.insert(brInst->getCondition()->getName());
								// errs()<<brInst->getCondition()->getName()<<"\n";
							}
							continue;
						}
						// if (instLiveVars.find(defName) == instLiveVars.end()) {
						universeVar.insert(defName);
						// errs()<<defName<<"\n";
						// }
					}
				}
			}
			// errs()<<"Number of instruction is : "<<instructionList.size()<<"\n";
			std::map<Instruction*, std::set<std::string>> defVariables;
			std::set<std::string> argDef;
			for (Function::arg_iterator args = F.arg_begin(), last = F.arg_end(); args != last ; args++) {
				Argument* arg = &(*args);
				Value *val = arg;
				argDef.insert(val->getName());
				// errs()<<val->getName()<<"\n";
			}
			Function::iterator firstBB = F.begin();
			BasicBlock::iterator firstInst = firstBB->begin();
			defVariables[&(*firstInst)] = argDef;
			bool modify = true;
			for (Function::iterator BB = F.begin(), EB = F.end(); BB != EB; BB++) {
				if (BB == F.begin())
					continue;
				for (BasicBlock::iterator inst = BB->begin(), ei = BB->end(); inst != ei; ++inst) {
					defVariables[&(*inst)].insert(universeVar.begin(), universeVar.end());
				}
			}
			while (modify) {
				modify = false;
				for (std::vector<Instruction*>::iterator inst = instructionList.begin(),
										ei = instructionList.end(); inst != ei; ++inst) {
					// getDefName(**inst);
					// errs()<<**inst<<"\n";
					std::string defName ("undef");
					if ((*inst)->isBinaryOp()) {
						defName = (*inst)->getName();
						// errs()<<defName<<"\n";
					}
					else if (auto* getElemPtrInst = dyn_cast<GetElementPtrInst>(*inst)) {
						defName = getElemPtrInst->getName();
						// errs()<<defName<<"\n";
					}
					else if (auto* storeInst = dyn_cast<StoreInst>(*inst)) {
						defName = (*inst)->getOperand(1)->getName();
						// errs()<<defName<<"\n";
					}
					else if (isa<AllocaInst>(**inst)||isa<ReturnInst>(**inst)||isa<BranchInst>(**inst)) {

					}
					else {
						defName = (*inst)->getName();
						// errs()<<defName<<"\n";
					}
					std::set<std::string> inSet;

					if (firstBlockInsts.find(*inst) != firstBlockInsts.end()) {
						// errs()<<**inst<<"\n";
						BasicBlock* block = (*inst)->getParent();

						pred_iterator neighbour = pred_begin(block);
						if (neighbour != pred_end(block)) {
							BasicBlock* neighbourBlock = *neighbour;
							Instruction* endInst = (Instruction*)neighbourBlock->getTerminator();

							std::set<std::string> defVarSet = defVariables[endInst];
							inSet.insert(defVarSet.begin(), defVarSet.end());
							

							for (pred_iterator last = pred_end(block); neighbour != last; ++neighbour) {
								neighbourBlock = *neighbour;
								endInst = (Instruction*)neighbourBlock->getTerminator();
								defVarSet = defVariables[endInst];

								std::vector<std::string> intersectSet;
								std::set_intersection(inSet.begin(), inSet.end(),
		                        defVarSet.begin(), defVarSet.end(),
		                        std::back_inserter(intersectSet));
								inSet.clear();
								inSet.insert(intersectSet.begin(), intersectSet.end());
								for (std::string n: intersectSet) {
									// errs()<<n<<"\n";
								}
							}
						}
					}
					else {
						std::vector<Instruction*>::iterator prevIt = inst - 1;
						std::set<std::string> prevDefVars = defVariables[(*prevIt)];

						inSet.insert(prevDefVars.begin(), prevDefVars.end());
					}
					if (defName.compare("undef"))
						inSet.insert(defName);//Now inSet is outSet
					if (defVariables[*inst] != inSet) {
						modify = true;
					}
					defVariables[*inst].clear();
					defVariables[*inst].insert(inSet.begin(), inSet.end());
				}
			}
			
			for (Function::iterator BB = F.begin(), EB = F.end(); BB != EB; BB++) {
				for (BasicBlock::iterator inst = BB->begin(), ei = BB->end(); inst != ei; ++inst) {
					// it = instructionList.insert(it, &(*inst));
					// errs()<<"{";

					errs()<<*inst<<"\t{";
					std::set<std::string> instLiveVars = defVariables[&(*inst)];
					for(User::op_iterator opIt = (inst)->op_begin(), opEnd = (inst)->op_end();
								opIt!=opEnd; ++opIt) {
						Value *opnd = *opIt;
						if (isa<AllocaInst>(*inst)||isa<BranchInst>(*inst)) {
							continue;
						}
						std::string useName (opnd->getName());
						if ((!useName.compare(""))||(!useName.compare("argc"))||(!useName.compare("argv"))) {
							continue;
						}
						if (isa<GlobalValue>(opnd)) {
							continue;
						}
						if (instLiveVars.find(useName) == instLiveVars.end()) {
							errs()<<useName<<", ";
						}
					}
					errs()<<"}\n\n";
					
					for (std::set<std::string>::iterator liveIt = instLiveVars.begin(), endIt = instLiveVars.end();
									liveIt != endIt; liveIt++) {
						// errs()<<*liveIt<<", ";
					}
					// errs()<<"}\n";
				}
			}
			opCounter.clear();
			return false;
		}
		std::string getDefName(Instruction inst) {
			if (inst.isBinaryOp()) {
				errs()<<inst<<"\n";
			}
			
		}
	};
}
char UnInitAnalysis::ID = 0;
static RegisterPass<UnInitAnalysis> X("uninitvars", "UnInitialized variable analysis Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);