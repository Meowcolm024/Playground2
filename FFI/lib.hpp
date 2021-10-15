#pragma once

extern "C"
{
    void hello(int);

    void printArr(const int *, int);

    int resetArray(int *, int);

    struct MyStruct
    {
        double d;
        char c;
        int32_t i;
    };

    void printStruct(const MyStruct*);
}
