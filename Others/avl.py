from dataclasses import dataclass
from typing import Any, Union


@dataclass
class Empty:
    pass


@dataclass
class Node:
    v: Any      # value
    l: 'AVL'    # left
    r: 'AVL'    # right
    d: int      # balance factor


AVL = Union[Empty, Node]

def height(t: AVL) -> int:
    if t == Empty:
        return 0
    return max(height(t.l), height(t.r)) + 1

def balance(t: AVL):
    if t == Empty:
        return Empty
    Node(v, l, r, d) = t
