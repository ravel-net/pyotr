config = {
    't1_config': {
        'network_name': 't1',
        'topo_dir': './networks/t1/whole_topo',
        'backup_links':[
            {'1':2, '2':2}, # dict(router: interface)
            {'2':3, 'w':2}
        ],
        'primary_links':[
            {'1':1, 'u':0}, # dict(router: interface)
            {'2':1, 'v':0}
        ],
        'one_link_fails':{
            'fail_link':{'1':1, 'u':0},
            'backup_link':{'2':3, 'w':2} #inactive
        },
        'another_link_fails':{
            'fail_link':{'2':1, 'v':0},
            'backup_link':{'1':2, '2':2} #inactive
        }
    },

    't2_config': {
        'network_name': 't2',
        'topo_dir': './networks/t2/whole_topo',
        'backup_links':[
            {'1':2, 'v':2}, # dict(router: interface)
            {'2':3, 'w':2}
        ],
        'primary_links':[
            {'1':1, 'u':0}, # dict(router: interface)
            {'2':1, 'v':0}
        ],
        'one_link_fails':{
            'fail_link':{'1':1, 'u':0},
            'backup_link':{'2':3, 'w':2} #inactive
        },
        'another_link_fails':{
            'fail_link':{'2':1, 'v':0},
            'backup_link':{'1':2, 'v':2} #inactive
        }
    },

    't3_config': {
        'network_name': 't3',
        'topo_dir': './networks/t3/whole_topo',
        'backup_links':[
            {'1':2, 'v':2}, # dict(router: interface)
            {'2':3, 'w':2}
        ],
        'primary_links':[
            {'1':1, '2':0}, # dict(router: interface)
            {'2':1, 'v':0}
        ],
        'one_link_fails':{
            'fail_link':{'1':1, '2':0},
            'backup_link':{'2':3, 'w':2} #inactive
        },
        'another_link_fails':{
            'fail_link':{'2':1, 'v':0},
            'backup_link':{'1':2, 'v':2} #inactive
        }
    },

    't4_config': {
        'network_name': 't4',
        'topo_dir': './networks/t4/whole_topo',
        'backup_links':[
            {'1':2, 'v':2}, # dict(router: interface)
            {'2':3, 'w':2}
        ],
        'primary_links':[
            {'1':1, '2':0}, # dict(router: interface)
            {'2':1, 'v':0}
        ],
        'one_link_fails':{
            'fail_link':{'1':1, '2':0},
            'backup_link':{'2':3, 'w':2} #inactive
        },
        'another_link_fails':{
            'fail_link':{'2':1, 'v':0},
            'backup_link':{'1':2, 'v':2} #inactive
        }
    }
}
