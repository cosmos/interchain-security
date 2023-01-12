# Method

Contains information about the differential/difference testing method in general and how it impacts the project.

Answers questions like:

- main motivation and concepts to used to create the framework
- your biggest influences in writing it (maybe some references to books, articlest etc)
- what tradeoff you had to make
- what do you think is missing with this approach (compared to other approaches)
- what you feel is the main benefit of the framework
- how to improve it in the future (ignore code related stuff, focus on concepts)
- other things you find important

# Main motivation

The motivation to do diff testing is the goal to find more, deeper, bugs in the long run life of the project in a more cost effective way than can be done by other testing methods (unit, full node, integration, model based testing).

Each of the traditional methods has draw backs

- unit\
Finds shallow bugs.
- full node\
Expensive to setup and run, hard to debug, slow.
- integration\
Limited to isolated parts of system so cannot find logic bugs across systems.
- model based\
Exhaustive model checkers do not scale well to large systems. Esoteric languages hard to onboard and maintain.

Diff testing should be

- Able to find deep bugs (and shallow ones)\
Complicated systems *may* have tricky, deep bugs which are caused by specific interleavings of API calls with specific params. We want a way to try to find these.
- Maintainable\
If the requirements change or a major piece of the system API changes it should be possible to modify existing test code to handle the new system, without having to scrap everything.
- Scalable\
Everything should run in memory, cheaply. It should be possible to use the debugger to step through failed tests.

Diff testing does not

- Try to find every bug\
Diff testing is based on randomness and heuristics and these can only get you so far in finding bugs. More on this later.

## Concepts

For this section we don't use any academic parlance, just the terminology as it is already being used in the project.

![diagram0](./diagrams/diagram0.png)
