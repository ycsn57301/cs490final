#pragma once
#include "ips.h"
#include "emp-tool/emp-tool.h"

class CrossChecking { public:
	vector<block> data;
	CrossChecking() {
	}
	template<typename T>
	void add(const T &x) {
		for(size_t i = 0; i < x.size(); ++i)
			data.push_back((block)x[i]);
	}
	void addBit(const Bit & x) {
		data.push_back((block)x);
	}

	// prover 				verifier
	//id1		pvio		id1
	//
	//id2		pvio		id2
	bool check(bool is_prover, bool is_one, int id1, int id2, int port, NetIO * pvio) {
		NetIO *io;//
		block tmp_delta;
		bool is_sender
		if(is_one) {
			io = new NetIO(nullptr, port);
			io->send_data(data.data(), sizeof(block)*data.size());
			io->flush();
			delete io;
		} else {
			io = new NetIO(is_prover?provers[id]:verifiers[id], port);
			block * tmp = new block[data.size()];
			io->recv_data(tmp, sizeof(block)*data.size());
			xorBlocks_arr(data.data(), tmp, data.data(), data.size());
			delete[] tmp;
			delete io;
			if(is_prover) {
				Hash h;
				h.put(tmp, sizeof(block)*data.size());
				char dgst[DIGEST_SIZE];
				h.digest(dgst);
				pvio->send_data(dgst, DIGEST_SIZE);
				pvio->flush();
			} else {
				Hash h, h2;
				h.put(tmp, sizeof(block)*data.size());
				char dgst[DIGEST_SIZE];
				char dgst2[DIGEST_SIZE];
				h.digest(dgst);
				pvio->recv_data(dgst2, DIGEST_SIZE);
				bool eq = memcmp(dgst, dgst2, DIGEST_SIZE) == 0;	
				if(!eq) return true;
			}
		}
		return false;
	}
};