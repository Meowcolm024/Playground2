from typing import *
from dataclasses import dataclass
from enum import Enum


class Flag(Enum):
    DELETED = -1
    EMPTY = 0
    ACTIVE = 1


@dataclass
class Cell:
    data: Any
    flag: Flag


class Table:
    table: list[Cell]
    capacity: int
    hf: Callable[[int, int], int]
    of: Callable[[int, int], int]
    size: int

    def __init__(self, capacity: int, hf: Callable[[int, int], int], of: Callable[[int, int], int]) -> None:
        self.table = [Cell(None, Flag.EMPTY) for _ in range(capacity)]
        self.capacity = capacity
        self.hf = hf
        self.of = of
        self.size = 0

    def isEmpty(self) -> int:
        return self.size == 0

    def isHalfFull(self) -> bool:
        return self.size > (self.capacity / 2)

    def search(self, key: int) -> int:
        i = 0
        this = (self.hf(key, self.capacity) + self.of(key, i)) % self.capacity
        for i in range(0, self.capacity-1):
            if self.table[this].flag == Flag.EMPTY:
                return -1
            if self.table[this].flag in [Flag.ACTIVE, Flag.DELETED]:
                # if next is hashed
                that = self.table[(self.hf(key, self.capacity) +
                                   self.of(key, i+1)) % self.capacity]
                if self.table[that].flag in [Flag.ACTIVE, Flag.DELETED]:
                    continue
                else:
                    return this
        return -1

    def insert(self, value: Any) -> None:
        if self.isHalfFull():
            self.rehash()

    def rehash(self) -> None:
        table = self.table.copy()
        self.table = [Cell(None, Flag.EMPTY) for _ in range(2*self.capacity+1)]
        for cell in table:
            self.insert()
