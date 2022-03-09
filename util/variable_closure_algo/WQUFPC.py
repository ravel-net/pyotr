import pprint

class WQUFPC:
  def __init__(self, variables):
  	self.N = len(variables)
  	self.id = []
  	self.sz = []
  	self.mapping = {}
  	self.reverse_mapping = []
  	for i in range(0,self.N):
  		self.sz.append(0)
  		self.id.append(i)
  		self.mapping[variables[i]] = i #maps variables to i
  		self.reverse_mapping.append(variables[i])

  def root(self, i):
  	while i != self.id[i]:
  		self.id[i] = self.id[self.id[i]]; # point to grandparent
  		i = self.id[i]
  	return i

  def connected(self, p, q):
  	return self.root(self.mapping[p]) == self.root(self.mapping[q])

  def union(self, p, q):
    i = self.root(self.mapping[p])
    j = self.root(self.mapping[q])
    if self.sz[i] < self.sz[j]:
      self.id[i] = j
      self.sz[j] += self.sz[i]
    elif i != j:
      self.id[j] = i
      self.sz[i] += self.sz[j]

  def connected_components(self):
    connected_components_list = {}
    for i in range(0,self.N):
      curr_root = self.root(i)
      if self.reverse_mapping[curr_root] not in connected_components_list:
        connected_components_list[self.reverse_mapping[curr_root]] = []
      connected_components_list[self.reverse_mapping[curr_root]].append(self.reverse_mapping[i])
    return connected_components_list