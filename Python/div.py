x = 0b0011_0001_0000_0000
y = 0b0000_0000_0111_0001

y = y << 1
print(bin(y))

for _ in range(8):
    add = 0b0
    if y >= x:
        y = y - x
        add = 0b1
    print(bin(y))
    y = y << 1
    y += add
    print(bin(y), "\n---")

print(bin(y))

quot = y & 0b0000_0000_1111_1111
rem = y & 0b1111_1111_0000_0000
rem = rem >> 9

print(bin(quot))
print(bin(rem))