-- GIFT: Geometric Integration of Fundamental Topologies
-- Main entry point for Lean 4 formalization
-- Version: 3.3.26 (455+ certified relations, 48 published axioms, axiom audit cleanup)

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
-- EXTENSIONS
-- ═══════════════════════════════════════════════════════════════════════════════

import GIFT.MollifiedSum   -- Cosine-squared kernel, mollified sum S_w(T)

-- Exploratory modules (not in published papers, separate from Certificate)
import GIFT.Exploratory.Sequences    -- Fibonacci, Lucas embeddings
import GIFT.Exploratory.Primes       -- Prime Atlas (direct, derived, Heegner)
import GIFT.Exploratory.Moonshine    -- Monstrous moonshine (Monster, j-invariant)
import GIFT.Exploratory.McKay        -- McKay correspondence, Golden emergence
import GIFT.Exploratory.Zeta         -- Riemann zeta correspondences (conjectures)
import GIFT.Exploratory.MollifiedSum -- GIFT adaptive cutoff (Riemann line, closed)
import GIFT.Exploratory.Spectral     -- Selberg/Connes bridges (Riemann line, closed)

-- ═══════════════════════════════════════════════════════════════════════════════
-- CERTIFICATE (modular: Foundations / Predictions / Spectral)
-- ═══════════════════════════════════════════════════════════════════════════════

import GIFT.Certificate.Core
