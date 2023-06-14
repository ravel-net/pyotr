import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
print(root)
from Core.Datalog.program import DT_Program
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table
import psycopg2 
import databaseconfig as cfg

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

def Example1():
  p1 = "G(x,z) :- A(x,z)\nG(x,z) :- G(x,y),G(y,z)"
  p2 = "G(x,z) :- A(x,z)\nG(x,z) :- A(x,y),G(y,z)"
  program1 = DT_Program(p1)
  program2 = DT_Program(p2)
  print(program1.contains(program2))
  print(program2.contains(program1))  

def Example2():
  p = "G(x,y,z) :- G(x,w,z),A(w,y),A(w,z),A(z,z),A(z,y)"   
  program = DT_Program(p)
  program.minimize()
  print(program)

def Example3():
  R = DT_Table(name="R", columns={"c0":"integer_faure"}, cvars={"x":"c0", "y":"c0", "z":"c0"})
  l = DT_Table(name="l", columns={"c0":"integer_faure"}, cvars={"x":"c0", "y":"c0", "z":"c0"})
  database = DT_Database(tables=[R,l])

  p1 = "l(x)[And(x != 2, x != 3)] :- R(x)[x != 2], R(x)[x != 3]\nl(x)[x != 2] :- R(x)[x != 2], R(x)"
  program1 = DT_Program(p1, database)
  program1.minimize(minimizeAtomsOn=False, minimizeRulesOn=True) # only rules minimized
  print(program1)
  database.delete(conn)

def Example4():
  R = DT_Table(name="R", columns={"c0":"integer_faure", "c1":"integer_faure"}, cvars={"y":"c1", "z":"c1"}, domain={"c0":['1', '2'], "c1":['1', '2']})
  L = DT_Table(name="L", columns={"c0":"integer_faure", "c1":"integer_faure", "c2":"integer_faure"}, cvars={"y":"c1", "z":"c1"}, domain={"c0":['1', '2'], "c1":['1', '2']})
  Q = DT_Table(name="Q", columns={"c0":"integer_faure"}, cvars={"y":"c0", "z":"c0"}, domain={"c0":['1', '2']})
  database = DT_Database(tables=[R,L,Q])
  p1 = "R(x,y) :- L(x,q,z), Q(z)\nR(x,y) :- L(x,q,z), Q(z)"
  program1 = DT_Program(p1, database)
  program1.minimize()
  database.delete(conn)

if __name__ == "__main__":
    Example1()
    Example2()
    Example3()
    Example4()
