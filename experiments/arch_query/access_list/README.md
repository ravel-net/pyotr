# Types of Access-lists

- only constrain source:
  - ```
    access-list 17 permit 171.64.17.224
    => 171.64.17.224, d, permit, s == 171.64.17.224

    access-list 39 permit 204.152.100.0 0.0.3.255
    => 204.152.100.0/0.0.3.255, d, permit, s == 204.152.100.0/0.0.3.255

    # allow source address except for 171.64.9.123, 171.64.9.125, 171.64.9.141
    access-list 110 deny   ip any host 171.64.9.123
    access-list 110 deny   ip any host 171.64.9.125
    access-list 110 deny   ip any host 171.64.9.141
    access-list 110 permit ip any any
    ```
- both constrain source and destination:
  - ```
    access-list 110 permit ip host 172.20.4.195 host 172.20.4.1
    => 172.20.4.195, 172.20.4.1, permit, s == 172.20.4.195 /\ d == 172.20.4.1

    access-list 110 permit ip host 172.20.4.195 host 172.20.4.1
    access-list 110 permit ip host 172.20.4.1 host 172.20.4.195
    

    access-list 100 permit ip 172.17.0.0 0.0.255.255 172.27.16.32 0.0.0.31
    access-list 100 deny   ip 172.17.0.0 0.0.255.255 any
    access-list 100 permit ip any any
    ```
- constrain ports
  - ```
    # allow ports [0, 134]\/(139, 445) \/(455, max)
    access-list 135 deny   tcp any any eq 445
    access-list 135 permit tcp any any gt 139
    access-list 135 deny   tcp any any gt 134
    access-list 135 permit tcp any any
    ```