from networkx.algorithms.link_prediction import cn_soundarajan_hopcroft
from networkx.classes.function import nodes
from db import DB
import networkx as nx
import random
from tqdm import tqdm
import math
import os
from rtable import Rtable
import psycopg2
import databaseconfig as cfg

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

tablename = "fwd_7018"
cursor.execute("select n1, n2 from {}".format(tablename))
links = cursor.fetchall()

G = nx.DiGraph(links)
ans = nx.is_directed_acyclic_graph(G)
print(ans)