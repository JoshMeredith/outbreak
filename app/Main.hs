{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Data.Array.Accelerate
import Data.Array.Accelerate.LLVM.Native as CPU
import Data.Array.Accelerate.LLVM.PTX    as PTX

import Criterion.Main

import qualified Prelude as P
import System.Environment


type TransmissionRate = Float
type RecoveryRate     = Float
type QuarantineRate   = Float


type PassengerFlow = Int


type SPop = Int
type IPop = Int
type RPop = Int


globalAirports :: Int
globalAirports = 3000

maxSteps :: Int
maxSteps = 10


main = defaultMain
         [ bench "CPU" $ whnf go population
--          , bench "PTX" $ whnf (PTX.run . outbreakN) population
         ]
-- main = P.print . CPU.run . sums . outbreak $ population
  where
    (population, outbreak) = makeOutbreak globalAirports

    !go = CPU.runN outbreakN

    outbreakN :: Acc (Vector SPop, Vector IPop, Vector RPop)
              -> Acc (Vector SPop, Vector IPop, Vector RPop)
    outbreakN = aiterate (constant maxSteps) outbreak
    sums vs =
      let (xs, ys, zs) = unlift vs
      in lift (sum $ flatten xs, sum $ flatten ys, sum $ flatten zs)


aiterate
  :: forall a. Arrays a
  => Exp Int
  -> (Acc a -> Acc a)
  -> Acc a
  -> Acc a
aiterate n f z
  = let
      step :: Acc (Scalar Int, a) -> Acc (Scalar Int, a)
      step v = let (i,x) = unlift v
               in  lift (map (+1) i, f x)
      --
      initial :: Acc (Scalar Int, a)
      initial = lift (unit 0, z)
    in
    asnd $ awhile (\v -> map (< n) (afst v)) step initial


makeOutbreak
  :: Int
  -> ( (Vector SPop, Vector IPop, Vector RPop)
     , Acc (Vector SPop, Vector IPop, Vector RPop) -> Acc (Vector SPop, Vector IPop, Vector RPop)
     )
makeOutbreak nAirports = (populations, stepOutbreak transmissions recoveries quarantines arrivals departures)
  where
    transmissions = use . fromList (Z :. nAirports) $ P.repeat 0.1
    recoveries    = use . fromList (Z :. nAirports) $ P.repeat 0.1
    quarantines   = use . fromList (Z :. nAirports) $ P.repeat 0.5
    flows         = use . fromList (Z :. nAirports :. nAirports) $ P.cycle [1..nAirports]
    susceptible   = fromList (Z :. nAirports) $ P.repeat 10000
    other         = fromList (Z :. nAirports) $ P.repeat 100
    populations   = (susceptible, other, other)
    arrivals      = sum flows
    departures    = sum $ transpose flows


stepOutbreak
  :: Acc (Vector TransmissionRate)
  -> Acc (Vector RecoveryRate)
  -> Acc (Vector QuarantineRate)
  -- -> Acc (Array DIM2 PassengerFlow)
  -> Acc (Vector PassengerFlow)
  -> Acc (Vector PassengerFlow)
  -> Acc (Vector SPop, Vector IPop, Vector RPop)
  -> Acc (Vector SPop, Vector IPop, Vector RPop)
stepOutbreak transmissions recoveries quarantines arrivals departures populations =
  lift (susceptible', infected', recovered')
  where
    (susceptible, infected, recovered) = unlift populations
    totals = zipWith3 (\s i r -> s + i + r) susceptible infected recovered
    --
    newlyInfected :: Acc (Vector IPop)
    newlyInfected = zipWith4 infect transmissions susceptible infected totals
    infect :: Exp TransmissionRate
           -> Exp SPop
           -> Exp IPop
           -> Exp RPop
           -> Exp IPop
    infect rate s i n = floor $ (rate * fromIntegral i * fromIntegral s)/(fromIntegral n)
    --
    newlyRecovered :: Acc (Vector RPop)
    newlyRecovered = zipWith recover recoveries infected
    recover rate i = floor $ rate * fromIntegral i
    --
    (quarantined, notQuarantined) = unzip $ zipWith quarantine iArrivals quarantines
    quarantine :: Exp IPop
               -> Exp QuarantineRate
               -> Exp (RPop, IPop)
    quarantine i rate = let q = floor $ rate * fromIntegral i in lift (q, i - q)
    --
    proportional :: Exp Int -> Exp Int -> Exp Int -> Exp Int
    proportional compartment n flow = floor passengers
      where
        passengers :: Exp Float
        passengers = (fromIntegral compartment / fromIntegral n) * fromIntegral flow
    --
    -- arrivals     = sum flows
    sArrivals    = zipWith3 proportional susceptible totals arrivals
    iArrivals    = zipWith3 proportional infected    totals arrivals
    rArrivals    = zipWith3 proportional recovered   totals arrivals
    --
    -- departures   = sum . transpose $ flows
    sDepartures  = zipWith3 proportional susceptible totals departures
    iDepartures  = zipWith3 proportional infected    totals departures
    rDepartures  = zipWith3 proportional recovered   totals departures
    --
    susceptible' = zipWith4 stepS susceptible newlyInfected sArrivals sDepartures
    stepS s newi a d = s - newi + a - d
    --
    infected'    = zipWith5 stepI infected newlyInfected newlyRecovered notQuarantined iDepartures
    stepI i newi newr notq d = i + newi - newr + notq - d
    --
    recovered'   = zipWith5 stepR recovered newlyRecovered rArrivals rDepartures quarantined
    stepR r newr a d q = r + newr + a - d + q
