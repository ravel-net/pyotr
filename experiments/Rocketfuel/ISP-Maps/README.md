# Rocketfuel
## Background
Rocketfuel dataset contains routing and topology information about different ISPs. Each ISP network is composed of multiple points of presence or POPs. Each POP is a physical location where the ISP houses a collection of routers. The ISP backbone connects these POPs, and the routers attached to inter-POP links are called backbone or core routers. Within every POP, access routers provide an intermediate layer between the ISP backbone and routers in neighboring networks. Rocketfuel contains ISP maps that consist of backbone, access, and directly connected neighboring domain routers along with the IP-level interconnections between them.

A generic POP has a few backbone routers in a densely connected mesh. In large POPs, backbone routers may not be connected in a full mesh. Backbone routers also connect to backbone routers in other POPs. Each access router connects to one or more routers from the neighboring domain and to two backbone routers for redundancy.

