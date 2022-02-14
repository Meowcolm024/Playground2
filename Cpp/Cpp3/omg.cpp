#include <iostream>
#include <vector>
#include <algorithm>

long vecToInt(const std::vector<int>& v)
{
	auto pw = [](int x) -> long {
		int acc = 1;
		for (int i = x-1; i > 0; i--)
			acc *= 10;
		return acc;
	};
	if (v.size() == 0)
		return 0;
	long acc = 0;
	for (int i = 0; i < v.size(); i++)
		acc += v[i] * pw(v.size() - i);
	return acc;
}

std::vector<int> intToVec(const long i)
{
	std::vector<int> tmp;
	long x = i;
	int c = 0;
	while (x != 0)
	{
		c = x % 10;
		x = x / 10;
		tmp.push_back(c);
	}
	std::reverse(tmp.begin(), tmp.end());
    if (tmp.size() == 0)
        tmp.push_back(0);
	return tmp;
}

int main()
{
    using namespace std;
    cout << vecToInt({2}) << endl;
    auto x = intToVec(0);
    for (auto i : x)
        cout << i;
    cout << endl;
    return 0;
}