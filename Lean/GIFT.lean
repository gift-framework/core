-- GIFT: Geometric Integration of Fundamental Topologies
-- Main entry point for Lean 4 formalization
-- Version: 5.0.0 (180+ certified relations + Hierarchy formula + Real Mathematics)

import GIFT.Algebra
import GIFT.Geometry
import GIFT.Topology
import GIFT.Relations
import GIFT.Certificate

-- V4.0: Mathematical Foundations (real content, not just arithmetic)
import GIFT.Foundations

-- V5.0: Algebraic Foundations (octonion-based derivation)
import GIFT.Algebraic

-- Topological Extension: +12 relations (25 total)
import GIFT.Relations.GaugeSector
import GIFT.Relations.NeutrinoSector
import GIFT.Relations.LeptonSector
import GIFT.Relations.Cosmology

-- Mass Factorization Theorem: +11 relations (v1.6.0)
import GIFT.Relations.MassFactorization

-- V2.0 New modules
import GIFT.Sequences      -- Fibonacci, Lucas, Recurrence
import GIFT.Primes         -- Prime Atlas (direct, derived, Heegner)
import GIFT.Moonshine      -- Monstrous moonshine (Monster group, j-invariant)
import GIFT.McKay          -- McKay correspondence, Golden emergence

-- V3.0: Joyce Perturbation Theorem
import GIFT.Sobolev            -- Sobolev spaces H^k
import GIFT.DifferentialForms  -- Exterior calculus
import GIFT.ImplicitFunction   -- Implicit function theorem
import GIFT.IntervalArithmetic -- Verified numerical bounds
import GIFT.Joyce              -- Torsion-free G2 existence

-- V4.0: Dimensional Hierarchy
import GIFT.Foundations.GoldenRatioPowers  -- phi^-2, phi^-54, 27^phi
import GIFT.Hierarchy                       -- Master hierarchy formula
