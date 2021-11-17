jsdata = {
    'Canada': 0.9,
    'Japan': 0.3
}

rt = '"Comfirmed cases<br>per million<br>"'


def gs(mx) -> str:
    result = ','.join(reversed(["{0:.2f}".format(mx/5*i) for i in range(6)]))
    return f"let gs = [" + result + "]"


def datapack(ds) -> str:
    return 'let datapack = {' + ','.join([f'"{k}": {v}' for k, v in ds.items()]) + '}'


with open("datapack.js", "w") as file:
    file.write(gs(0.67))
    file.write("\n")
    file.write(datapack(jsdata))
    file.write("\nlet reportTitle = " + rt + "\n")