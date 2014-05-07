# Makefile for GFJ

COQ_ARGS := -impredicative-set
COQ := coqc $(COQ_ARGS)

all : FJ_tactics.vo Functors.vo Names.vo Arith.vo Bool.vo \
	PNames.vo Lambda.vo Arith_Lambda.vo Bool_Lambda.vo \
	Mu.vo NatCase.vo tests

FJ_tactics.vo : FJ_tactics.v
	$(TIME) coqc FJ_tactics.v

Functors.vo : FJ_tactics.vo Functors.v
	$(TIME) $(COQ) Functors.v 

Names.vo : FJ_tactics.vo Functors.vo Names.v
	$(TIME) $(COQ) Names.v 

PNames.vo : FJ_tactics.vo Functors.vo Names.vo PNames.v
	$(TIME) $(COQ) PNames.v 

Arith.vo : FJ_tactics.vo Functors.vo Names.vo Arith.v
	$(TIME) $(COQ) Arith.v 

Lambda.vo : FJ_tactics.vo Functors.vo Names.vo PNames.vo Lambda.v
	$(TIME) $(COQ) Lambda.v 

NatCase.vo : FJ_tactics.vo Functors.vo Names.vo Arith.vo PNames.vo NatCase.v
	$(TIME) $(COQ) NatCase.v 

Arith_Lambda.vo : FJ_tactics.vo Functors.vo Names.vo Arith.vo Lambda.vo PNames.vo Arith_Lambda.v
	$(TIME) $(COQ) Arith_Lambda.v 

Bool_Lambda.vo : FJ_tactics.vo Functors.vo Names.vo Bool.vo Lambda.vo PNames.vo Bool_Lambda.v
	$(TIME) $(COQ) Bool_Lambda.v 

Bool.vo : FJ_tactics.vo Functors.vo Names.vo Bool.v
	$(TIME) $(COQ) Bool.v 

Mu.vo : FJ_tactics.vo Functors.vo Names.vo PNames.vo Mu.v
	$(TIME) $(COQ) Mu.v

test_A.vo : FJ_tactics.vo Functors.vo Names.vo Arith.vo test_A.v
	$(TIME) $(COQ) test_A.v

test_AB.vo : FJ_tactics.vo Functors.vo Names.vo Arith.vo Bool.vo test_AB.v
	$(TIME) $(COQ) test_AB.v

test_AL.vo : FJ_tactics.vo Functors.vo Names.vo Arith.vo Lambda.vo Arith_Lambda.vo PNames.vo test_AL.v
	$(TIME) $(COQ) test_AL.v

test_BL.vo : FJ_tactics.vo Functors.vo Names.vo Bool.vo Lambda.vo Bool_Lambda.vo PNames.vo test_BL.v
	$(TIME) $(COQ) test_BL.v

test_ABL.vo : FJ_tactics.vo Functors.vo Names.vo Arith.vo Lambda.vo PNames.vo Arith_Lambda.vo\
	Bool_Lambda.vo test_ABL.v
	$(TIME) $(COQ) test_ABL.v

MiniML.vo : FJ_tactics.vo Functors.vo Names.vo Arith.vo Lambda.vo PNames.vo Arith_Lambda.vo\
	Bool_Lambda.vo Mu.vo NatCase.vo MiniML.v
	$(TIME) $(COQ) MiniML.v

tests : test_A.vo test_AB.vo test_AL.vo test_BL.vo test_ABL.vo MiniML.vo

clean : 
	rm *.vo *.glob



