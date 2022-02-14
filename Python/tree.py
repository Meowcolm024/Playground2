from dataclasses import dataclass
from typing import Any


@dataclass
class Node:
    value: Any
    left: Any
    right: Any


class Tree:
    def __init__(self) -> None:
        self.nodes = None

    def insert(self, key):
        def __insert__(node: Node, key) -> Node:
            if node is None:
                return Node(key, None, None)
            if node.value > key:
                return Node(node.value, __insert__(node.left, key), node.right)
            else:
                return Node(node.value, node.left, __insert__(node.right, key))
        self.nodes = __insert__(self.nodes, key)
        return self

    def delete(self, key):
        def __delMax__(node: Node):
            if node is None:
                return None
            if node.right is None:
                return (node.value, node.left)
            (m, r) = __delMax__(node.right)
            return (m, Node(node.value, node.left, r))
        def __delete__(node: Node, key) -> Node:
            if node is None:
                return None
            if node.value == key:
                if node.right is None:
                    return node.left
                else:
                    (m, r) = __delMax__(node.right)
                    return Node(m, node.left, r)
            if node.value > key:
                return Node(node.value, __delete__(node.left, key), node.right)
            else:
                return Node(node.value, node.left, __delete__(node.right, key))
        self.nodes = __delete__(self.nodes, key)
        return self

    def toList(self) -> list:
        def __toList__(node: Node) -> list:
            if node is None:
                return []
            return __toList__(node.left) + [node.value] + __toList__(node.right)
        return __toList__(self.nodes)


test = Tree().insert(5).insert(6).insert(4).delete(4).insert(2).toList()

print(test)
