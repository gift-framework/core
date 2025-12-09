-- GIFT: Geometric Integration of Fundamental Topologies
-- Main entry point for Lean 4 formalization
-- Version: 3.0.0 (165+ certified relations + Joyce existence)

import GIFT.Algebra
import GIFT.Geometry
import GIFT.Topology
import GIFT.Relations
import GIFT.Certificate

-- Topological Extension: +12 relations (25 total)
import GIFT.Relations.GaugeSector
import GIFT.Relations.NeutrinoSector
import GIFT.Relations.LeptonSector
import GIFT.Relations.Cosmology

-- Mass Factorization Theorem: +11 relations (v1.6.0)
import GIFT.Relations.MassFactorization

-- V2.0 New modules
import GIFT.Sequences      -- Fibonacci, Lucas, Recurrence
import GIFT.Primes         -- Prime Atlas (Tier 1-4, Heegner, Special)
import GIFT.Monster        -- Monster group dimension, j-invariant
import GIFT.McKay          -- McKay correspondence, Golden emergence

-- V3.0: Joyce Perturbation Theorem
import GIFT.Sobolev            -- Sobolev spaces H^k
import GIFT.DifferentialForms  -- Exterior calculus
import GIFT.ImplicitFunction   -- Implicit function theorem
import GIFT.IntervalArithmetic -- Verified numerical bounds
import GIFT.Joyce              -- Torsion-free G2 existence
