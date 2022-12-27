#include <algorithm>
#include <cassert>
#include <cerrno>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <vector>

#include <unistd.h>

using namespace std;

#ifndef __dead
#define __dead
#endif

static int all;
static int debug;
static int quick;

#define d(level, x) \
	do { \
		int lvl = (level); \
		if (debug >= lvl) { \
			cerr << '[' << lvl << "] " << __func__ << ": "; \
			x ; \
		} \
	} while(0)


template <typename T>
std::ostream& operator << (std::ostream& os, const std::vector<T>& v) {
	os << "[";
	for (auto &&item : v)
		os << " " << item;
	os << " ]";
	return os;
}


template<typename T>
struct trans {
	T		source;
	vector<T>	parts;

	T lost(T split_width) const {
		if (parts.empty())
			return T();
		T v = source + split_width;
		for (auto p : parts)
			v -= p + split_width;
		d(2, cerr << "returning " << v << " for source " << source << " and parts " << parts << endl);
		return v;
	}
};

template <typename T>
std::ostream& operator << (std::ostream& os, const trans<T> &tr) {
	return os << tr.source << " => " << tr.parts;
}

// `have` and `want` must be sorted
template<typename T>
vector<trans<T>> squash_same(vector<T> &have, vector<T> &want) {
	auto i = have.begin();
	auto j = want.begin();
	vector<trans<T>> squashed;

	while (i != have.end() && j < want.end()) {
		if (*j < *i)
			j++;
		else if (*j > *i)
			i++;
		else {
			trans<T> tr;
			tr.source = *i;
			tr.parts.push_back(*j);
			squashed.push_back(tr);
			i = have.erase(i);
			j = want.erase(j);
		}
	}
	d(1, cerr << "found " << squashed.size() << " same items" << endl);
	return squashed;
}

template<typename T>
struct state {
	vector<trans<T>> &best;
	vector<trans<T>> &current;
	vector<T> &have;
	vector<T> &want;
	vector<trans<T>> same;
	const T split_width;

	// caches
	const T have_sum;
	T best_left;

	// other stuff
	size_t nsolutions;
	bool first_printed;

	state(vector<trans<T>> &best_, vector<trans<T>> &current_, vector<T> &have_, vector<T> &want_, const T split_width_)
		: best(best_)
		, current(current_)
		, have(have_)
		, want(want_)
		, same(squash_same(have, want))
		, split_width(split_width_)
		, have_sum(accumulate(have.begin(), have.end(), T()))
		, best_left(T())
		, nsolutions(0)
		, first_printed(false)
	{ }

	// returns true IFF `current` was better than `best`.
	bool update_best() {
		auto left = have_sum - accumulate(current.begin(), current.end(), T(),
		    [this](T sum, const trans<T> &tr) { return sum + tr.source - tr.lost(split_width); });
		d(2, cerr << "best_left=" << best_left << ", left=" << left << endl);
		if (left <= best_left)
			return false;
		nsolutions++;
		best = current;
		best_left = left;
		d(1, cerr << "new best: " << best << endl);
		if (all)
			print_best();
		return true;
	}

	void print_best() const {
		if (!first_printed)
			cout << right;
		else
			cout << "--" << endl;

		for (auto &&res : same) {
			cout << setw(7) << res.source << ':';
			for (auto part : res.parts) {
				cout << ' ' << part;
			}
			cout << endl;
		}

		for (auto &&res : best) {
			cout << setw(7) << res.source << ':';
			for (auto part : res.parts) {
				cout << ' ' << part;
			}
			cout << endl;
		}
	}
};

template<typename T> bool try_next_have(state<T> &state);
template<typename T> bool try_next_want(state<T> &state, T left);

template<typename T>
bool try_next_have(state<T> &state) {
	d(1, cerr << "have=" << state.have << endl);

	if (state.have.empty())
		return false;

	T prev {};
	for (auto i = state.have.begin(); i != state.have.end(); i++) {
		T avail = *i;
		assert(avail > 0);
		if (avail == prev)
			continue;	// optimization
		else
			prev = avail;
		trans<T> tr { avail };

		state.current.push_back(tr);
		i = state.have.erase(i);
		if (try_next_want(state, avail))
			return true;
		i = state.have.insert(i, avail);
		state.current.pop_back();
	}
	return false;
}

template<typename T>
bool try_next_want(state<T> &state, T left) {
	d(1, cerr << "want=" << state.want << endl);

	T prev {};
	for (auto j = state.want.begin(); j != state.want.end() && *j <= left; j++) {
		assert(*j > 0);
		if (*j == prev)
			continue;
		prev = *j;

		T nleft = left - *j;
		state.current.back().parts.push_back(*j);
		j = state.want.erase(j);
		if (state.want.empty()) {
			if (state.update_best() && quick)
				return true;
		} else if (nleft > state.split_width) {
			if (try_next_want(state, nleft - state.split_width))
				return true;
			if (try_next_have(state))
				return true;
		}
		j = state.want.insert(j, state.current.back().parts.back());
		state.current.back().parts.pop_back();
	}

	// Check what happen if we simply ignore the last source choosen by try_next_have().
	// This may become better option sometimes when split_width is non-zero.
	if (try_next_have(state))
		return true;
	return false;
}

template<typename T>
bool find_best_split(vector<T> have, vector<T> want, T split_width) {
	sort(have.begin(), have.end());
	sort(want.begin(), want.end());

	vector<trans<T>> best;
	vector<trans<T>> current;

	d(1, cerr << "have: " << have << endl);
	d(1, cerr << "want: " << want << endl);

	state s(best, current, have, want, split_width);
	try_next_have(s);

	if (s.nsolutions == 0) {
		cerr << "no solution" << endl;
		return false;
	}

	if (!all)
		s.print_best();
	return true;
}

__dead
void usage(const string &msg = "") {
	if (!msg.empty())
		cerr << getprogname() << ": " << msg << endl;
	cerr << "usage: " << getprogname() << " [-d] [-a | -q] have want [split_width]" << endl; 
	exit(1);
}

// read array of values
template<typename T>
vector<T> slurp(const char *path, const string &name) {
	ifstream fs(path);
	if (!fs) {
		cerr << "failed to open '" << name << "' file: " << strerror(errno) << endl;
		exit(2);
	}

	T v;
	vector<T> result;
	d(3, cerr << "begin: " << name << endl);
	for (fs >> v; !fs.eof(); fs >> v) {
		d(3, cerr << "v=" << v << endl);
		if ((T() - T(1) < T()) && v <= 0 ||
		    (T() - T(1) > T()) && v >= (T() - T(1))/2) {
			cerr << "invalid " << name << " value detected" << endl;
			exit(3);
		}
		result.push_back(v);
	}
	d(3, cerr << "end: " << name << endl);
	return result;
}

int main(int argc, char **argv) {
	int split_width, ch;

	while ((ch = getopt(argc, argv, "adq")) != -1) {
		switch (ch) {
		case 'a':
			all = 1;
			break;
		case 'd':
			debug++;
			break;
		case 'q':
			quick = 1;
			break;
		default:
			usage();
		}
	}
	argc -= optind;
	argv += optind;

	if (all && quick)
		usage();

	if (argc < 2 || argc > 3)
		usage();

	if (argc == 3) {
		if ((split_width = atoi(argv[2])) <= 0)
			usage("invalid split width");
	}

	auto have = slurp<unsigned long>(argv[0], "have");
	auto want = slurp<unsigned long>(argv[1], "want");

	return find_best_split(have, want, (unsigned long)split_width) ? 0 : 1;
}
