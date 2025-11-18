---
title: "The many-worlds interpretation"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy of science
  - physics
...


## Presentation

Some phenomenons uncovered by quantum physicists have not been found to be deterministic: leading the (at least seemingly) same experiment leads to different outcomes, which apparently follow a probability distribution. As the physical world was considered deterministic until there by classical physics, an interpretation was proposed to render the results of quantum mechanics in a deterministic frame: [the many-wrolds interpretation](https://en.wikipedia.org/wiki/Many-worlds_interpretation). The idea is to claim something difficultly provable or refutable: the fact that each outcome possible according to our physical theory which does not happen in our world does indeed happen, but in another world.

--MATH_START--
Throughout this page, let $T$ be the set of instants in the unfolding of time. If $t, t' \in T$, $t \le t'$ means that the instant $t$ is before (or simultaneous with) $t'$. \
Let $S$ be the set of states and $W$ the set of worlds.

Some definitions in [this article](https://www.leibnizproject.com/Articles/physical_theories.html) are used.
--MATH_END--

[//]: # Rocq (13-16)


## Indeterminism

According to [our definition](https://www.leibnizproject.com/Articles/physical_theories.html), we can conclude that a physical theory isn't deterministic whenever two histories of events coinciding at a certain instant must coincide every time after.

--MATH_START--
$\mathbf{Definition}$\
Let $pt$ a physical theory in ${\{⊥ ,⊤\}}^{S^T}$. \
An indeterminism in $pt$ is a $(h_1, h_2, t_0, t) \in {S^T \times S^T \times T \times T}$ such that:
$$\begin{cases*}
  t_0 \lt t \\
  pt \text{ satisfies } h_1 \\
  pt \text{ satisfies } h_2 \\
  h_1(t_0) = h_2(t_0) \\
  h_1(t) \neq h_2(t)
\end{cases*}$$
Let $I(pt)$ be the set of indeterminisms of $pt$. \
And let $W = {\{⊥ ,⊤\}}^{I(pt)}$ be the set of worlds.
--MATH_END--

[//]: # Rocq (18-45)

--MATH_START--
$\mathbf{Lemma}$\
A physical theory $pt$ is deterministic if and only if $I(pt) = \emptyset$.

$\mathbf{proof:}$\
Direct application of the definitions of a deterministic physical theory and of an indeterminism. \
■
--MATH_END--

[//]: # Rocq (47-86)


## A deterministic many-worlds interpretation

To get rid of indeterminisms of a physical theory, we define a world for each possible outcome in each instance of indeterminism.

--MATH_START--
$\mathbf{Definition}$\
Let $pt$ a physical theory in ${\{⊥ ,⊤\}}^{S^T}$. \
The many-worlds extension is the physical theory $\bar pt \in {\{⊥ ,⊤\}}^{(S^W)^T}$ defined below:
$$\begin{align*}
    (S^W)^T &\to \mathbb \{⊥ ,⊤\} \\
    \bar h &\mapsto \begin{cases*}
        ⊥ \text{ if } \exists ind=(h_1, h_2, t_0, t) \in I(pt), w \in W \text{ such that } (w(ind) \text{ and } \forall t' \in T, \bar h(t')(w) = h_2(t')) \text{ or } (\neg w(ind) \text{ and } \forall t' \in T, \bar h(t')(w) = h_1(t')) \\
        \forall w \in W, pt(t \mapsto \bar h(t)(w)) \text{ otherwise}
    \end{cases*}
\end{align*}$$
--MATH_END--

[//]: # Rocq (88-97)

--MATH_START--
$\mathbf{Lemma}$\
The many-worlds extension of any physical theory is deterministic.

$\mathbf{proof:}$\
Let $pt$ a physical theory in ${\{⊥ ,⊤\}}^{S^T}$ and $\bar pt$ its many-worlds extension. \
Let's reason by contradiction and suppose that: \
$$\begin{cases*}
  t_0 \lt t \\
  \bar pt \text{ satisfies } \bar h_1 \\
  \bar pt \text{ satisfies } \bar h_2 \\
  \bar h_1(t_0) = \bar h_2(t_0) \\
  \bar h_1(t) \neq \bar h_2(t)
\end{cases*}$$
The two staisfiabilities and the definition of $\bar pt$ imply that
$$\tag{1} \forall w \in W, ind=(h_1, h_2, t_0, t) \in I(pt),
\begin{cases*}
  \neg ((w(ind) \text{ and } \forall t' \in T, \bar h_1(t')(w) = h_2(t')) \text{ or } (\neg w(ind) \text{ and } \forall t' \in T, \bar h_1(t')(w) = h_1(t'))) \\
  \forall w \in W, pt(t' \mapsto \bar h_1(t')(w)) \\
  \neg ((w(ind) \text{ and } \forall t' \in T, \bar h_2(t')(w) = h_2(t')) \text{ or } (\neg w(ind) \text{ and } \forall t' \in T, \bar h_2(t')(w) = h_1(t'))) \\
  \forall w \in W, pt(t' \mapsto \bar h_2(t')(w))
\end{cases*}$$
As $\bar h_1(t) \neq \bar h_2(t)$, there is a $w \in W$ such that $\bar h_1(t)(w) \neq \bar h_2(t)(w)$. And as $\bar h_1(t_0) = \bar h_2(t_0)$, we have $\bar h_1(t_0)(w) = \bar h_2(t_0)(w)$. \
Moreover, equations 2 and 4 in $(1)$ imply that $pt$ satisfies $t' \mapsto \bar h_1(t')(w)$ and $t' \mapsto \bar h_2(t')(w)$. \
Thus we have an indeterminism $(t' \mapsto \bar h_1(t')(w), t' \mapsto \bar h_2(t')(w), t_0, t) \in I(pt)$. \
Applying equations 1 and 3 in $(1)$ to $w$ and this indeterminism gives
$$\begin{cases*}
  \neg ((w(ind) \text{ and } \forall t' \in T, \bar h_1(t')(w) = (t' \mapsto \bar h_2(t')(w))(t')) \text{ or } (\neg w(ind) \text{ and } \forall t' \in T, \bar h_1(t')(w) = (t' \mapsto \bar h_1(t')(w))(t'))) \\
  \neg ((w(ind) \text{ and } \forall t' \in T, \bar h_2(t')(w) = (t' \mapsto \bar h_2(t')(w)(t')) \text{ or } (\neg w(ind) \text{ and } \forall t' \in T, \bar h_2(t')(w) = (t' \mapsto \bar h_1(t')(w)))(t')))
\end{cases*}$$
That is
$$\begin{cases*}
  \neg ((w(ind) \text{ and } \forall t' \in T, \bar h_1(t')(w) = \bar h_2(t')(w)) \text{ or } (\neg w(ind) \text{ and } \forall t' \in T, \bar h_1(t')(w) = \bar h_1(t')(w))) \\
  \neg ((w(ind) \text{ and } \forall t' \in T, \bar h_2(t')(w) = \bar h_2(t')(w)) \text{ or } (\neg w(ind) \text{ and } \forall t' \in T, \bar h_2(t')(w) = h_1(t')(w)))
\end{cases*}$$
As $\bar h_1(t)(w) \neq \bar h_2(t)(w)$, this gives
$$\begin{cases*}
  \neg \neg w(ind) \\
  \neg w(ind)
\end{cases*}$$
and therefore a contradiction. \
■
--MATH_END--

[//]: # Rocq (99-173)
