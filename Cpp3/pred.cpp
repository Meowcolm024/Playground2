#include <algorithm>
#include <ctime>
#include <iostream>

using namespace std;

int main()
{
    constexpr auto arrSize = 32768u;
    int data[arrSize];
    for (auto c = 0; c < arrSize; c++)
        data[c] = rand() % 256;

    // sort(data, data + arrSize);

    auto start = clock();
    long sum = 0;
    for (auto i = 0; i < 100000; i++)
    {
        for (auto c = 0; c < arrSize; c++)
        {
            if (data[c] > 128)
                sum += data[c];
        }
    }

    auto et = static_cast<double>(clock() - start) / CLOCKS_PER_SEC;

    cout << et << endl;
}
