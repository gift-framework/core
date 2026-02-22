-- GIFT: Geometric Integration of Fundamental Topologies
-- Main entry point for Lean 4 formalization
-- Version: 4.0.0 (290+ certified relations, modular certificate structure)

-- ═══════════════════════════════════════════════════════════════════════════════
-- CORE & RELATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

import GIFT.Core
import GIFT.Relations
import GIFT.Relations.GaugeSector
import GIFT.Relations.NeutrinoSector
import GIFT.Relations.LeptonSector
import GIFT.Relations.Cosmology
import GIFT.Relations.MassFactorization

-- ═══════════════════════════════════════════════════════════════════════════════
-- MATHEMATICAL FOUNDATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

import GIFT.Foundations
import GIFT.Algebraic
import GIFT.Geometry

-- Joyce existence theorem
import GIFT.Sobolev
import GIFT.DifferentialForms
import GIFT.ImplicitFunction
import GIFT.IntervalArithmetic
import GIFT.Joyce

-- Dimensional hierarchy & golden ratio
import GIFT.Foundations.GoldenRatioPowers
import GIFT.Hierarchy

-- ═══════════════════════════════════════════════════════════════════════════════
-- OBSERVABLES & SPECTRAL THEORY
-- ═══════════════════════════════════════════════════════════════════════════════

import GIFT.Observables
import GIFT.Spectral

-- ═══════════════════════════════════════════════════════════════════════════════
-- EXTENSIONS (standalone modules, compiled but not in Certificate)
-- ═══════════════════════════════════════════════════════════════════════════════

import GIFT.Sequences      -- Fibonacci, Lucas, Recurrence
import GIFT.Primes         -- Prime Atlas (direct, derived, Heegner)
import GIFT.Moonshine      -- Monstrous moonshine (Monster group, j-invariant)
import GIFT.McKay          -- McKay correspondence, Golden emergence
import GIFT.MollifiedSum   -- Cosine-squared kernel, mollified sum S_w(T)

-- ═══════════════════════════════════════════════════════════════════════════════
-- CERTIFICATE (modular: Foundations / Predictions / Spectral)
-- ═══════════════════════════════════════════════════════════════════════════════

import GIFT.Certificate.Core
