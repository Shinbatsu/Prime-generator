# Prime Generation in Agda

This project implements **prime number generation** in Agda using **coinductive sorted streams** and well-founded recursion over a strict total order.

## Overview

The core idea is to represent sequences of numbers satisfying a predicate (e.g. "is prime") as an infinite, **sorted stream** with the ability to construct new streams by merging, filtering, and subtracting them based on logical conditions.