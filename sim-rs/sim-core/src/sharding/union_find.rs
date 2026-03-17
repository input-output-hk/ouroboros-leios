use std::collections::HashMap;

use crate::config::NodeId;

pub fn find(parent: &mut HashMap<NodeId, NodeId>, mut x: NodeId) -> NodeId {
    while parent[&x] != x {
        let grandparent = parent[&parent[&x]];
        parent.insert(x, grandparent);
        x = grandparent;
    }
    x
}

pub fn union(parent: &mut HashMap<NodeId, NodeId>, a: NodeId, b: NodeId) {
    let ra = find(parent, a);
    let rb = find(parent, b);
    if ra != rb {
        parent.insert(ra, rb);
    }
}
