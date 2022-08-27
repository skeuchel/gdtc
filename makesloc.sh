#!/bin/bash

function coqwc2 () {
  cat $* | coqwc | tail -n 1 | awk '{print ($1+$2)}'
}

FRAMEWORK="GDTC.v GDTC/Containers.v GDTC/Equality.v GDTC/FJ_tactics.v GDTC/Functors.v GDTC/Polynomial.v"
TYPESAFETY="CaseStudy/Names.v CaseStudy/PNames.v"
FEATURES="CaseStudy/Arith_Lambda.v CaseStudy/Arith.v CaseStudy/Bool_Lambda.v CaseStudy/Bool.v CaseStudy/Lambda.v CaseStudy/Mu.v CaseStudy/NatCase.v"
COMPOSITION="CaseStudy/MiniML.v CaseStudy/test_ABL.v CaseStudy/test_AB.v CaseStudy/test_AL.v CaseStudy/test_A.v CaseStudy/test_BL.v"

echo "FRAMEWORK        " $(coqwc2 $FRAMEWORK   2> /dev/null)
echo "TYPESAFETY       " $(coqwc2 $TYPESAFETY  2> /dev/null)
echo "FEATURES         " $(coqwc2 $FEATURES    2> /dev/null)
echo "COMPOSITION      " $(coqwc2 $COMPOSITION 2> /dev/null)
