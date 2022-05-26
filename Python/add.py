x = 0b01011010_00000000
y = 0b00000000_01110001

z = (x >> 8) *y

for _ in range(8):
    print(bin(y))
    if str(bin(y))[-1] == '1':
        y += x
    y = y >> 1

print(bin(y))
