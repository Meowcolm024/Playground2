#include <iostream>
using namespace std;

void swap(int &x, int &y)
{
    int tmp = y;
    y = x;
    x = tmp;
}

int partition(int xs[], int l, int r)
{
    int t = l;
    for (int i = l + 1; i < r; i++)
    {
        if (xs[i] < xs[l])
        {
            t++;
            swap(xs[t], xs[i]);
        }
    }
    swap(xs[t], xs[l]);
    return t;
}

void sort(int xs[], int l, int r)
{
    if (l >= r)
        return;
    int m = partition(xs, l, r);
    sort(xs, l, m);
    sort(xs, m + 1, r);
}

int main()
{
    int xs[] = {4, 3, 6, 7, 2, 0, 9, 8, 1, 5};
    sort(xs, 0, 10);
    for (auto i : xs)
        cout << i << " ";
    cout << endl;
    return 0;
}
