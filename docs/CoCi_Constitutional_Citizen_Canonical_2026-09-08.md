# CoCi Constitutional Citizen — Canonical Formal Definition

**Status:** Canonical formal specification draft, frozen 2026-09-08. External novelty is not asserted; novelty remains subject to adversarial prior-art and formal reduction analysis.

## Definitive definition

Let the Constitutional Calculus be
\[
\mathcal C=(X,U,T,\Omega,C,\pi,Q,\bar T,\rho,\mathcal W).
\]
A **Constitutional Citizen (CoCi)** is a constructively generated quotient-level inhabitant \(c\in Q\) for which a constitutional witness \(w_c\) establishes the minimum constitutional obligations:
\[
\operatorname{CoCi}_{\mathcal C}(c,w_c)\iff
\begin{cases}
c\in Q,\\
\exists x\in X:\pi(x)=c,\\
\operatorname{Adm}_{\mathcal C}(c,u)\Rightarrow\bar T(c,u)\in Q,\\
\pi(T(x,u))=\bar T(\pi(x),u),\\
\pi(\rho(c))=c,\\
\operatorname{Invariant}_{\mathcal C}(c),\\
\operatorname{Witness}_{\mathcal C}(w_c,c),\\
\operatorname{Constitutional}(w_c).
\end{cases}
\]

**Canonical sentence:** A CoCi is a constructively generated quotient inhabitant whose identity, lawful transformations, invariants, reconstruction, and witness are constitutionally closed and bidirectionally related to the underlying system.

## Constitutional Convex

\[
\mathfrak K_{\mathcal C}=\{c\in Q:\operatorname{CoCi}_{\mathcal C}(c)\}.
\]

“Convex” initially denotes the closed admissible constitutional region. Strict geometric convexity is a separate theorem obligation and is not assumed.

## Minimum constitutional dimensions

\[
\mathcal D_C=(I,D,T,A,\Omega,W,\rho)
\]

where identity, domain membership, lawful transformation, admissibility, invariant/observable structure, constructive witness, and reverse reconstruction are the candidate minimum dimensions.

Minimality is not asserted until deletion-counterexample proofs establish indispensability of each component.

## Micro-bidirectional closure

Every primitive CoCi function \(f\) must have:
\[
\boxed{\mathsf{MB}(f)=(F_f,R_f,I_f,W_f)}
\]

with forward execution \(F_f\), reverse/reconstruction \(R_f\), invariant preservation \(I_f\), and independent witness \(W_f\). A function is not closed CoCi mathematics until all four obligations are satisfied.

## Construction

\[
\operatorname{Construct}_{\mathcal C}:D_C\subseteq X\to Q,
\qquad
\operatorname{Construct}_{\mathcal C}(x)=\pi(x).
\]

## Transformation and rights

\[
\bar T:Q\times U\to Q,
\qquad
A_C(c)=\{u\in U:\operatorname{Adm}_{\mathcal C}(c,u)\}.
\]

A CoCi has only constitutionally derived transformation capabilities. The fundamental descent law is
\[
\boxed{\pi\circ T_u=\bar T_u\circ\pi}.
\]

## Responsibilities

For every admitted transformation \(c\xrightarrow{u}c'\), the Citizen must preserve quotient membership, descent correspondence, declared invariants, witnessability, and reconstruction:
\[
c'\in Q,\quad \pi(T(x,u))=c',\quad \Omega_Q(c')=\Omega_Q^*(c,u),\quad W(c,u,c'),\quad \pi(\rho(c'))=c'.
\]

Thus:
\[
\boxed{\text{right to transform}\Longleftrightarrow\text{responsibility to remain constitutional}.}
\]

## Bidirectional construction

\[
x\overset{\pi}{\longrightarrow}c\overset{\rho}{\longrightarrow}[x]_{\sim_C},
\qquad \boxed{\pi(\rho(c))=c}.
\]

This is constitutional reversibility, not microscopic invertibility.

## Recursive closure

For an input sequence \(\mathbf u\):
\[
\boxed{\forall n\ge0:\pi\circ T_{\mathbf u}^{\,n}=\bar T_{\mathbf u}^{\,n}\circ\pi}.
\]

## Witness

\[
w_c=\operatorname{Witness}_{\mathcal C}(c),\qquad
w_c\vdash_{\mathcal C}\operatorname{CoCi}(c),\qquad
\operatorname{Constitutional}(w_c).
\]

The Citizen cannot certify itself by proclamation.

## Constitutional Convict

A Constitutional Convict is a constructive constitutional-failure object
\[
\operatorname{CoConvict}_{\mathcal C}(x,d,w_d)
\]
where \(d\) is an explicitly demonstrated constitutional defect and \(w_d\) witnesses that defect. Failure of proof alone is insufficient.

## Separation of levels

\[
\boxed{\text{Physical Person}\neq\text{CoCi}\neq\text{Quotient State}.}
\]

Formal constitutional proofs apply to mathematical representations unless an explicit realization theorem establishes physical correspondence.

## Minimality theorem program

For every \(f\in\mathcal D_C\), construct \(\operatorname{CoCi}^{-f}\) and seek
\[
\exists x_f:\operatorname{CoCi}^{-f}(x_f)\not\Rightarrow\operatorname{CoCi}(x_f).
\]

Target theorem:
\[
\boxed{\operatorname{MinimalCoCi}}.
\]

Until machine-checked, minimality remains a theorem target.

## Governing principles

**Nothing is a Citizen because we call it one.**

**A thing becomes a Citizen by satisfying the minimum Constitution, and remains a Citizen only through constitutionally closed transformation.**

**A Convict is not something merely lacking approval; it carries a demonstrated constitutional defect.**

**The quotient is the constitutional semantic identity space; the CoCi is its witnessed inhabitant.**
