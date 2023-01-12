# Rocketfuel
## Background
Rocketfuel dataset contains routing and topology information about different ISPs. Each ISP network is composed of multiple points of presence or POPs. Each POP is a physical location where the ISP houses a collection of routers. The ISP backbone connects these POPs, and the routers attached to inter-POP links are called backbone or core routers. Within every POP, access routers provide an intermediate layer between the ISP backbone and routers in neighboring networks. Rocketfuel contains ISP maps that consist of backbone, access, and directly connected neighboring domain routers along with the IP-level interconnections between them.

A generic POP has a few backbone routers in a densely connected mesh. In large POPs, backbone routers may not be connected in a full mesh. Backbone routers also connect to backbone routers in other POPs. Each access router connects to one or more routers from the neighboring domain and to two backbone routers for redundancy.

## Dataset
### ISP-Maps
The folder ISP-Maps contains the map of 10 ISPs (1221, 1239, 1755, 2914, 3257, 3356, 3967, 4755, 6461, 7018). The file relevant to the topology is (See README.cch in the folder) is [AS].r1.cch where [AS] is one of the 10 AS numbers. This file contains the routers of an ISP with a "fringe" of radius 1 around the backbone and gateway routers.  This is the dataset used primarily in the Rocketfuel paper because it is expected to be robust to problems in recovering the ISP's naming convention and it shows the most relevant structure, without router chains leading to customers.

The ISP Map file contains a list of access and boundary routers including both internal and external links. Each router is identified using a uid. We can generate the internal topology of an ISP using this file.

### PoP-level ISP maps
The POP-level ISP maps are in the "AS-links" folder and contain links between POPs. These can be links between the different POPs of the same ISP or links between POPs owned by different ISPs. We are interested in links between POPs of different ISPs.

## Extracting Topology
The internal topology of ISPs can easily be extracted by parsing the ISP-maps. The difficulty is in extracting links of ISP with neighbouring ISPs. We can extract the location of these links from the POP-level ISP maps but information about the end routers is not available. Given an ISP X, if we want to find its links with another ISP Z, we can see the locations of ISP X with which ISP Z is connected to. Then for each link between ISP Z and X, we pick a random access router from the location and connect the ISPs. 
