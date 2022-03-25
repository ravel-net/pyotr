import BDD_managerModule
import encodeCUDD 

# BDD_managerModule.initialize(3)

# tauto = "^(&($(4,2),$(2,3)),^(&(~(2),$(2,3)),^($(4,3),^(~(3),^(&(~(4),$(2,3)),^(&(~(4),$(2,3)),^(&(~(2),$(3,2)),^(~(2),^(&(~(2),$(2,3)),^(&(~(2),$(2,3)),^(&(~(3),$(3,2)),~(3))))))))))))"
# tauto_idx = BDD_managerModule.str_to_BDD(tauto)
# print("tauto:", BDD_managerModule.evaluate(tauto_idx))

# contrd = "&(^(^(~(2),^(&(~(2),~(4)),^(&(~(4),~(3)),^(~(4),~(3))))),^(~(3),^(~(4),^(~(2),^(&(~(4),&(~(3),~(2))),^(~(2),^(&(~(2),~(4)),^(&(~(4),~(2)),&(~(3),~(2)))))))))),&(~(3),3))"
# contrd_idx = BDD_managerModule.str_to_BDD(contrd)
# print("contrd:", BDD_managerModule.evaluate(contrd_idx))

# sat = "^(&(^(^(^(^(~(2),^(&(~(2),~(4)),^(&(~(4),~(3)),^(~(4),~(3))))),^(~(3),^(~(4),^(~(2),^(&(~(4),&(~(3),~(2))),^(~(2),^(&(~(2),~(4)),^(&(~(4),~(2)),&(~(3),~(2)))))))))),^(~(3),^(~(4),~(2)))),^(~(3),^(~(4),^(&(~(3),~(2)),^(&(~(4),~(2)),^(~(2),~(2))))))),&($(2,3),3)),^(&($(4,3),3),^(3,3)))"
# sat_idx = BDD_managerModule.str_to_BDD(sat)

# OR_idx = BDD_managerModule.operate_BDDs(tauto_idx, sat_idx, '^')
# res = BDD_managerModule.evaluate(OR_idx)
# print("res:", res)

# And_idx = BDD_managerModule.operate_BDDs(contrd_idx, sat_idx, '&')
# print(BDD_managerModule.evaluate(And_idx))

domain = ['1', '2']
BDD_managerModule.initialize(3)
condition = 'And(x != 2)'
encoded_condition, variable_array = encodeCUDD.convertToCUDD(condition, domain)
print(encoded_condition)

print(BDD_managerModule.evaluate(BDD_managerModule.str_to_BDD(encoded_condition)))