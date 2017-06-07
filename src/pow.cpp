// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "pow.h"

#include "chain.h"
#include "chainparams.h"
#include "primitives/block.h"
#include "uint256.h"
#include "util.h"
#include <math.h>

const int64_t multiAlgoDiffChangeTarget = 570000;
const int64_t nDiffChangeTarget = 5;

static const int64_t nTargetTimespan =  8 * 10 * 60; // Legacy 4800
static const int64_t nTargetSpacing = 10 * 60; // 60 seconds 600
static const int64_t nInterval = nTargetTimespan / nTargetSpacing; // 8
//static const int64_t nTargetTimespanMulti = 1 * 61; // 61 Seconds
//static const int64_t nTargetSpacingMulti = 1 * 61; // 61 seconds
//static const int64_t nIntervalMulti = nTargetTimespanMulti / nTargetSpacingMulti; // 1 block

//MultiAlgo Target updates
static const int64_t multiAlgoNum = 5; // Amount of algos
static const int64_t multiAlgoTimespan = 61; // Time per block per algo
static const int64_t multiAlgoTargetSpacing = multiAlgoNum * multiAlgoTimespan; // NUM_ALGOS * 61 seconds

static const int64_t nAveragingInterval = 10; // 10 blocks
static const int64_t nAveragingTargetTimespan = nAveragingInterval * multiAlgoTargetSpacing; // 10* NUM_ALGOS * 61

static const int64_t nMaxAdjustDown = 40; // 40% adjustment down
static const int64_t nMaxAdjustUp = 20; // 20% adjustment up
static const int64_t nMaxAdjustDownV3 = 16; // 16% adjustment down
static const int64_t nMaxAdjustUpV3 = 8; // 8% adjustment up
static const int64_t nMaxAdjustDownV4 = 16;
static const int64_t nMaxAdjustUpV4 = 8;
static const int64_t nLocalDifficultyAdjustment = 4; //difficulty adjustment per algo
static const int64_t nLocalTargetAdjustment = 4; //target adjustment per algo

static const int64_t nMinActualTimespan = nAveragingTargetTimespan * (100 - nMaxAdjustUp) / 100;
static const int64_t nMaxActualTimespan = nAveragingTargetTimespan * (100 + nMaxAdjustDown) / 100;

static const int64_t nMinActualTimespanV3 = nAveragingTargetTimespan * (100 - nMaxAdjustUpV3) / 100;
static const int64_t nMaxActualTimespanV3 = nAveragingTargetTimespan * (100 + nMaxAdjustDownV3) / 100;

static const int64_t nMinActualTimespanV4 = nAveragingTargetTimespan * (100 - nMaxAdjustUpV4) / 100;
static const int64_t nMaxActualTimespanV4 = nAveragingTargetTimespan * (100 + nMaxAdjustDownV4) / 100;

const CBlockIndex* GetLastBlockIndexForAlgo(const CBlockIndex* pindex, int algo)
{
	for (;;)
	{
		if (!pindex)
			return NULL;
		if (pindex->GetAlgo() == algo)
			return pindex;
		pindex = pindex->pprev;
	}
	return NULL;
}

unsigned int static KimotoGravityWell(const CBlockIndex* pindexLast, const CBlockHeader *pblock, uint64_t TargetBlocksSpacingSeconds, uint64_t PastBlocksMin, uint64_t PastBlocksMax, int algo) {
          /* current difficulty formula, megacoin - kimoto gravity well */
          const CBlockIndex *BlockLastSolved = pindexLast;
          const CBlockIndex *BlockReading = pindexLast;
          const CBlockHeader *BlockCreating = pblock;

          BlockCreating = BlockCreating;

          uint64_t PastBlocksMass = 0;
          int64_t PastRateActualSeconds = 0;
          int64_t PastRateTargetSeconds = 0;
          double PastRateAdjustmentRatio = double(1);
          CBigNum PastDifficultyAverage;
          CBigNum PastDifficultyAveragePrev;
          double EventHorizonDeviation;
          double EventHorizonDeviationFast;
          double EventHorizonDeviationSlow;

      if (BlockLastSolved == NULL || BlockLastSolved->nHeight == 0 || (uint64_t)BlockLastSolved->nHeight < PastBlocksMin) { return Params().ProofOfWorkLimit(algo).GetCompact(); }

          for (unsigned int i = 1; BlockReading && BlockReading->nHeight > 0; i++) {
                  if (PastBlocksMax > 0 && i > PastBlocksMax) { break; }
                  PastBlocksMass++;

                  if (i == 1) { PastDifficultyAverage.SetCompact(BlockReading->nBits); }
                    else { PastDifficultyAverage = ((CBigNum().SetCompact(BlockReading->nBits) - PastDifficultyAveragePrev) / i) + PastDifficultyAveragePrev; }
                  PastDifficultyAveragePrev = PastDifficultyAverage;

                  PastRateActualSeconds = BlockLastSolved->GetBlockTime() - BlockReading->GetBlockTime();
                  PastRateTargetSeconds = TargetBlocksSpacingSeconds * PastBlocksMass;
                  PastRateAdjustmentRatio = double(1);
                  if (PastRateActualSeconds < 0) { PastRateActualSeconds = 0; }
                  if (PastRateActualSeconds != 0 && PastRateTargetSeconds != 0) {
                    PastRateAdjustmentRatio = double(PastRateTargetSeconds) / double(PastRateActualSeconds);
                  }
                  EventHorizonDeviation = 1 + (0.7084 * pow((double(PastBlocksMass)/double(144)), -1.228));
                  EventHorizonDeviationFast = EventHorizonDeviation;
                  EventHorizonDeviationSlow = 1 / EventHorizonDeviation;

                  if (PastBlocksMass >= PastBlocksMin) {
                          if ((PastRateAdjustmentRatio <= EventHorizonDeviationSlow) || (PastRateAdjustmentRatio >= EventHorizonDeviationFast)) { assert(BlockReading); break; }
                  }
                  if (BlockReading->pprev == NULL) { assert(BlockReading); break; }
                  BlockReading = BlockReading->pprev;
          }

          CBigNum bnNew(PastDifficultyAverage);
          if (PastRateActualSeconds != 0 && PastRateTargetSeconds != 0) {
                  bnNew *= PastRateActualSeconds;
                  bnNew /= PastRateTargetSeconds;
          }

          if (bnNew > Params().ProofOfWorkLimit(algo))
              bnNew = Params().ProofOfWorkLimit(algo);

      /// debug print
      //LogPrintf("Difficulty Retarget KGW\n");
      //LogPrintf("PastRateAdjustmentRatio = %g\n", PastRateAdjustmentRatio);
      //LogPrintf("Before: %08x  %s\n", BlockLastSolved->nBits, CBigNum().SetCompact(BlockLastSolved->nBits).getuint256().ToString().c_str());
      //LogPrintf("After:  %08x  %s\n", bnNew.GetCompact(), bnNew.getuint256().ToString().c_str());

      LogPrintf("KGW %g  %08x  %08x  %s\n" , PastRateAdjustmentRatio, BlockLastSolved->nBits, bnNew.GetCompact(), bnNew.getuint256().ToString().c_str());

          return bnNew.GetCompact();
  }

unsigned int static GetNextWorkRequired_Original(const CBlockIndex* pindexLast, const CBlockHeader *pblock, int algo)
  {
      unsigned int nProofOfWorkLimit = Params().ProofOfWorkLimit(algo).GetCompact();

      // Genesis block
      if (pindexLast == NULL)
          return nProofOfWorkLimit;

      if (pindexLast->nHeight+1 < 135)
          return nProofOfWorkLimit;

      // Only change once per interval
      if ((pindexLast->nHeight+1) % nInterval != 0)
      {
          // Special difficulty rule for testnet:
          if (TestNet())
          {
              // If the new block's timestamp is more than 2* 10 minutes
              // then allow mining of a min-difficulty block.
              if (pblock->nTime > pindexLast->nTime + nTargetSpacing*2)
                  return nProofOfWorkLimit;
              else
              {
                  // Return the last non-special-min-difficulty-rules-block
                  const CBlockIndex* pindex = pindexLast;
                  while (pindex->pprev && pindex->nHeight % nInterval != 0 && pindex->nBits == nProofOfWorkLimit)
                      pindex = pindex->pprev;
                  return pindex->nBits;
              }
          }
          return pindexLast->nBits;
      }

      // 51% mitigation, courtesy of Art Forz
      int blockstogoback = nInterval-1;
      if ((pindexLast->nHeight+1) != nInterval)
          blockstogoback = nInterval;

      // Go back by what we want to be 14 days worth of blocks
      const CBlockIndex* pindexFirst = pindexLast;
      for (int i = 0; pindexFirst && i < blockstogoback; i++)
          pindexFirst = pindexFirst->pprev;
      assert(pindexFirst);

      // Limit adjustment step
      int64_t nActualTimespan = pindexLast->GetBlockTime() - pindexFirst->GetBlockTime();
      LogPrintf("  nActualTimespan = %d  before bounds\n", nActualTimespan);

           int64_t nActualTimespanMax = ((nTargetTimespan*75)/50);
           int64_t nActualTimespanMin = ((nTargetTimespan*50)/75);

      if (nActualTimespan < nActualTimespanMin)
          nActualTimespan = nActualTimespanMin;
      if (nActualTimespan > nActualTimespanMax)
          nActualTimespan = nActualTimespanMax;

      // Retarget
      CBigNum bnNew;
      bnNew.SetCompact(pindexLast->nBits);
      bnNew *= nActualTimespan;
      bnNew /= nTargetTimespan;

      if (bnNew > Params().ProofOfWorkLimit(algo))
          bnNew = Params().ProofOfWorkLimit(algo);

      /// debug print
      LogPrintf("GetNextWorkRequired RETARGET\n");
      LogPrintf("nTargetTimespan = %d    nActualTimespan = %d \n", nTargetTimespan, nActualTimespan);
      LogPrintf("Before: %08x  %s\n", pindexLast->nBits, CBigNum().SetCompact(pindexLast->nBits).getuint256().ToString().c_str());
      LogPrintf("After:  %08x  %s\n", bnNew.GetCompact(), bnNew.getuint256().ToString().c_str());

      LogPrintf("RETARGET %d  %d  %08x  %08x  %s\n", nTargetTimespan, nActualTimespan, pindexLast->nBits, bnNew.GetCompact(), bnNew.getuint256().ToString().c_str());

      return bnNew.GetCompact();
  }

unsigned int static GetNextWorkRequired_KGW(const CBlockIndex* pindexLast, const CBlockHeader *pblock, int algo)
{
        static const int64_t BlocksTargetSpacing = 5 * 60; // 1 Minute
        unsigned int TimeDaySeconds = 60 * 60 * 24;
        int64_t PastSecondsMin = TimeDaySeconds * 0.5;
        int64_t PastSecondsMax = TimeDaySeconds * 14;
        uint64_t PastBlocksMin = PastSecondsMin / BlocksTargetSpacing;
        uint64_t PastBlocksMax = PastSecondsMax / BlocksTargetSpacing;

        return KimotoGravityWell(pindexLast, pblock, BlocksTargetSpacing, PastBlocksMin, PastBlocksMax, algo);
}

static unsigned int GetNextWorkRequiredMULTI(const CBlockIndex* pindexLast, const CBlockHeader *pblock, int algo)
{
	unsigned int nProofOfWorkLimit = Params().ProofOfWorkLimit(algo).GetCompact();

	//if (TestNet())
	//{
	//	// Testnet minimum difficulty block if it goes over normal block time.
	//	if (pblock->nTime > pindexLast->nTime + nTargetSpacing*2)
	//		return nProofOfWorkLimit;
	//	else
	//	{
	//		// Return the last non-special-min-difficulty-rules-block
	//		const CBlockIndex* pindex = pindexLast;
	//		while (pindex->pprev && pindex->nHeight % nInterval != 0 && pindex->nBits == nProofOfWorkLimit)
	//			pindex = pindex->pprev;
	//		return pindex->nBits;
	//	}
	//}

	LogPrintf("GetNextWorkRequired RETARGET\n");
	LogPrintf("Algo: %s\n", GetAlgoName(algo));
	LogPrintf("Height (Before): %s\n", pindexLast->nHeight);

	// find first block in averaging interval
	// Go back by what we want to be nAveragingInterval blocks per algo
	const CBlockIndex* pindexFirst = pindexLast;
	for (int i = 0; pindexFirst && i < NUM_ALGOS*nAveragingInterval; i++)
	{
		pindexFirst = pindexFirst->pprev;
	}

	const CBlockIndex* pindexPrevAlgo = GetLastBlockIndexForAlgo(pindexLast, algo);
	if (pindexPrevAlgo == NULL || pindexFirst == NULL)
	{
		LogPrintf("Use default POW Limit\n");
		return nProofOfWorkLimit;
	}

	// Limit adjustment step
	// Use medians to prevent time-warp attacks
	int64_t nActualTimespan = pindexLast-> GetMedianTimePast() - pindexFirst->GetMedianTimePast();
	nActualTimespan = nAveragingTargetTimespan + (nActualTimespan - nAveragingTargetTimespan)/4;

	LogPrintf("nActualTimespan = %d before bounds\n", nActualTimespan);

	if (nActualTimespan < nMinActualTimespanV4)
		nActualTimespan = nMinActualTimespanV4;
	if (nActualTimespan > nMaxActualTimespanV4)
		nActualTimespan = nMaxActualTimespanV4;

	//Global retarget
	CBigNum bnNew;
	bnNew.SetCompact(pindexPrevAlgo->nBits);

	bnNew *= nActualTimespan;
	bnNew /= nAveragingTargetTimespan;

	//Per-algo retarget
	int nAdjustments = pindexPrevAlgo->nHeight + NUM_ALGOS - 1 - pindexLast->nHeight;
	if (nAdjustments > 0)
	{
		for (int i = 0; i < nAdjustments; i++)
		{
			bnNew *= 100;
			bnNew /= (100 + nLocalTargetAdjustment);
		}
	}
	else if (nAdjustments < 0)//make it easier
	{
		for (int i = 0; i < -nAdjustments; i++)
		{
			bnNew *= (100 + nLocalTargetAdjustment);
			bnNew /= 100;
		}
	}

	if(bnNew > Params().ProofOfWorkLimit(algo))
	{
		LogPrintf("New nBits below minimum work: Use default POW Limit\n");
		return nProofOfWorkLimit;
	}

  LogPrintf("MULTI %d  %d  %08x  %08x  %s\n", multiAlgoTimespan, nActualTimespan, pindexLast->nBits, bnNew.GetCompact(), bnNew.getuint256().ToString().c_str());

	return bnNew.GetCompact();
}

unsigned int GetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock,int algo)
{
    int DiffMode = 1;

    if (TestNet()) {
      if (pindexLast->nHeight+1 < 50) { DiffMode = 1;
       } else if (pindexLast->nHeight + 1 < 100) {
          DiffMode = 2;
       } else {
          DiffMode = 3;
       }
    }else{
      if (pindexLast->nHeight+1 <= 5400) { DiffMode = 1;
      } else if (pindexLast->nHeight + 1 <= multiAlgoDiffChangeTarget) {
          DiffMode = 2;
       } else {
          DiffMode = 3;
       }
    }

    if (DiffMode == 1) {
        return GetNextWorkRequired_Original(pindexLast, pblock, algo);
    } else if (DiffMode == 2) {
        return GetNextWorkRequired_KGW(pindexLast, pblock, algo);
    } else if (DiffMode == 3) {
        return GetNextWorkRequiredMULTI(pindexLast, pblock, algo);
    }

    return GetNextWorkRequiredMULTI(pindexLast, pblock, algo);
}

bool CheckProofOfWork(uint256 hash, unsigned int nBits,int algo)
{
	CBigNum bnTarget;
	bnTarget.SetCompact(nBits);

	// Check range
	if (bnTarget <= 0 || bnTarget > Params().ProofOfWorkLimit(algo))
		return error("CheckProofOfWork(algo=%d) : nBits (%08x) below minimum work (%08x)", algo, bnTarget.GetCompact(), Params().ProofOfWorkLimit(algo).GetCompact());

	// Check proof of work matches claimed amount
	if (hash > bnTarget.getuint256())
		return error("CheckProofOfWork(algo=%d) : hash doesn't match nBits", algo);

	return true;
}

uint256 GetBlockProof(const CBlockIndex& block)
{
    uint256 bnTarget;
    bool fNegative;
    bool fOverflow;
    bnTarget.SetCompact(block.nBits, &fNegative, &fOverflow);
    if (fNegative || fOverflow || bnTarget == 0)
        return 0;
    // We need to compute 2**256 / (bnTarget+1), but we can't represent 2**256
    // as it's too large for a uint256. However, as 2**256 is at least as large
    // as bnTarget+1, it is equal to ((2**256 - bnTarget - 1) / (bnTarget+1)) + 1,
    // or ~bnTarget / (nTarget+1) + 1.
    return (~bnTarget / (bnTarget + 1)) + 1;
}
