# iptables-analyze

Build a model of iptables firewalls and analyze them with Z3

# What

iptables-analyze takes a set of iptables rules and builds a model of them using the python Z3 bindings.

# Why

I find it difficult to reason about iptables changes:

  * Could the existing set of rules be simplified?
  * Are there redundant entries?
  * What effect does a change to the rules actually have?
  * Are these two sets of rules identical?

Instead we can build a logical model of the set of firewall rules and use Z3 to answer these questions.

# How

Each firewall rule is a set of constraints on the following inputs for IPv4:

  * Source IP CIDR (32-bit + mask)
  * Source IP Port (16-bit)
  * Destionation IP CIDR (32-bit + mask)
  * Destionation IP Port (16-bit)
  * Protocol (8-bit)

TODO: describe output as a state machine that connects chains

TODO: describe "default drop, first match" semantics.

iptables can be modeled by a function is the conjunction of each rule -- i.e. each set of constrained input tuples are short-circuit boolean OR'd together.

With this model we can:

  * Check if a specific connection should be accepted or rejected
  * Check if a two models of different firewalls are equivalent and if the aren't provide counter-examples
  * Check if a model meets specific constraints on rules

# Additional Reading

* [Initial hacker news comment that described a system like this](https://news.ycombinator.com/item?id=12374471)
* Microsoft whitepaper that described a system like this - [Automated Analysis and Debugging of Network Connectivity Policies](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/secguru.pdf)
* [Z3 - a tutorial](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.225.8231&rep=rep1&type=pdf)
* [Z3 API in Python](http://www.cs.tau.ac.il/~msagiv/courses/asv/z3py/guide-examples.htm)

# TODO

* [ ] Fill out this README
* [x] Link to original Azure whitepaper
* [ ] Pull apart functionality to separte files and functions
* [ ] Add basic sanity tests
* [ ] Build out iptables rules parser
* [ ] Build out usecases
   * [ ] Check a single connection against a model
   * [ ] Check static contracts against a model
   * [ ] Check two models for equivalence
   * [ ] Simplify an existing model
   * [ ] Check connectivity with multiple models
