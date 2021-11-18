int bye(int z) {
    int p = 10*z;
    int q = 5+z;
    return p + q;
}

int hello(int i, int j) {
    int tmp = 0;
    if (i > j) {
        tmp = i * 10;
    } else {
        tmp = i / 10;
    }
    return tmp;
}
