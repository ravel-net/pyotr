import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
from Core.Homomorphism.Datalog.unify import unify

def minimizeAtoms(P):        
    for ruleNum in range(P.numRules):
        rule = P.getRule(ruleNum)
        atomNum = 0
        while atomNum < rule.numBodyAtoms:
            if rule.numBodyAtoms == 1: # if only one atom left in program, stop minimizing redundant atoms
                break

            rule_with_deleted_atom = rule.copyWithDeletedAtom(atomNum)
            if not rule_with_deleted_atom.safe():
                atomNum += 1 
                continue
            contained = P.contains_rule(rule_with_deleted_atom)
            if contained:
                P.replaceRule(ruleNum, rule_with_deleted_atom) 
                rule = rule_with_deleted_atom
            else:
                atomNum += 1   

def minimizeRules(P):
    ruleNum = 0
    while ruleNum < P.numRules: # replace for loop to while loop to avoid ruleNum out of list after deleting a rule
        if P.numRules == 1: # if only one rule left in program, stop minimizing
            return
        rule = P.getRule(ruleNum)
        newProgram = P.copyWithDeletedRule(ruleNum)
        if newProgram.contains_rule(rule):
            P.deleteRule(ruleNum)
        else:
            ruleNum += 1   

def enhancedMinimization(P):
    signatureBuckets = {}
    ruleName = {}
    P_unified = []
    for ruleNum, rule in enumerate(P._rules):
        signature = rule.getSignature()
        if not signature in signatureBuckets:
            signatureBuckets[signature] = ([],[]) # (rule, ruleNum)
        signatureBuckets[signature][0].append(rule)
        signatureBuckets[signature][1].append("r"+str(ruleNum))
    for signature in signatureBuckets:
        bucket = signatureBuckets[signature][0]
        ruleNums = signatureBuckets[signature][1]
        # for i in range(len(bucket)-1):
        i = 0
        while i < len(bucket):
            j = i+1
            # for j in range(i+1, len(bucket)-1):
            while j < len(bucket):
                r1 = bucket[i]
                r2 = bucket[j]
                r_tmp = unify(r1, r2, ruleNums[i])
                if (r_tmp != None): # unification was successful
                    bucket[i] = r_tmp
                    del bucket[j]
                    del ruleNums[j]
                else:
                    j += 1
            i += 1
        for rule in bucket: # add all unified rules to p_unified
            P_unified.append(str(rule))
    P.replaceProgram(P_unified)


