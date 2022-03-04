DdNode *x1_0, *x2_0, *x3_0, *x3_1 
x1_0 = Cudd_bddNewVar(gbm);
x2_0 = Cudd_bddNewVar(gbm);
x3_0 = Cudd_bddNewVar(gbm);
x3_1 = Cudd_bddNewVar(gbm);
Cudd_bddAnd(gbm,Cudd_bddOr(gbm,Cudd_bddOr(gbm,x1_1,Cudd_bddOr(gbm,Cudd_bddAnd(gbm,x1_1,x2_1),Cudd_bddOr(gbm,Cudd_bddAnd(gbm,x2_1,Cudd_bddAnd(gbm,x3_0,Not(x3_1))),Cudd_bddOr(gbm,x2_1,Cudd_bddAnd(gbm,x3_0,Not(x3_1)))))),Cudd_bddOr(gbm,Cudd_bddAnd(gbm,x3_0,Not(x3_1)),Cudd_bddOr(gbm,x2_1,Cudd_bddOr(gbm,x1_1,Cudd_bddOr(gbm,Cudd_bddAnd(gbm,x2_1,Cudd_bddAnd(gbm,Cudd_bddAnd(gbm,x3_0,Not(x3_1)),x1_1)),Cudd_bddOr(gbm,x1_1,Cudd_bddOr(gbm,Cudd_bddAnd(gbm,x1_1,x2_1),Cudd_bddOr(gbm,Cudd_bddAnd(gbm,x2_1,x1_1),Cudd_bddAnd(gbm,Cudd_bddAnd(gbm,x3_0,Not(x3_1)),x1_1))))))))),Cudd_bddAnd(gbm,Cudd_bddAnd(gbm,x3_0,Not(x3_1)),Cudd_bddAnd(gbm,Not(x3_0),x3_1)))

Or(1,Or(1,Or(x1_0,Or(1,Or(1,Or(1,Or(x1_0,Or(1,Or(1,Or(1,x1_0))))))))))