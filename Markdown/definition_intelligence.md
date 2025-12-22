---
title: "A definition of intelligence"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
...


## Presentation

Here is formalized the concept of intelligence of an agent in a deterministic evironment.

One relies on [this article](https://leibnizproject.com/Articles/occam_razor.html).

--MATH_START--
Throughout this page, let $T$ be the set of instants in the unfolding of time. If $t, t' \in T$, $t \le t'$ means that the instant $t$ is before (or simultaneous with) $t'$. \
Let $S$ be the set of states and $A$ the set of actions the agent can do.
--MATH_END--

[//]: # Rocq (7-10)


## Policies

A policy is a line of conduct: what the agent will do depending on the situation.

--MATH_START--
$\mathbf{Definition}$\
The set $P$ of policies is the set of functions from histories before some instant to actions.

$\mathbf{Definition}$\
A history is said to follow a policy if actions done at each instant is the one given by the policy. \
With $t_0 \in T$, a history before $t_0$ is said to follow a policy before $t_0$ if actions done at each instant before $t_0$ is the one given by the policy.
--MATH_END--

[//]: # Rocq (12-31)

Given a goal, one establishes a policy in order to reach it.

--MATH_START--
$\mathbf{Definition}$\
The set $STR$ of strategizings is the set of functions from events (goals) to policies.
--MATH_END--

[//]: # Rocq (33-34)


## Goal fulfilling, adequateness to reach goals and intelligence

A policy is more adequate than another to reach a goal if its failure implies the failure of the other one. And one is more intelligent if one elaborates a more adequate policy whatever the goal.

These two definitions don't work in [non-deterministic environments](https://leibnizproject.com/Articles/physical_theories.html). If instead there is some randomness, a goal may be reached thanks to beginner's luck: an action which is not the most likely to achieve the goal may succeed because something unexpected (but still possible) happened.

--MATH_START--
$\mathbf{Definition}$\
A goal is said fulfilled in a history before $t_0 \in T$ by a policy $p \in P$ if it is achieved while the policy is followed.
--MATH_END--

[//]: # Rocq (36-41)

--MATH_START--
$\mathbf{Definition}$\
A policy $p_1 \in P$ is said more adequate than $p_2 \in P$ to achieve a goal $g$ if
$$g \text{ is fulfilled in some history following } p_2 \Rightarrow g \text{ is fulfilled in some history following } p_1$$
--MATH_END--

[//]: # Rocq (43-61)

--MATH_START--
$\mathbf{Definition}$\
A strategizing $str_1 \in STR$ is said more intelligent than $str_2 \in STR$ if, whatever the goal, it provides a more adequate policy.
--MATH_END--

[//]: # Rocq (63-82)
