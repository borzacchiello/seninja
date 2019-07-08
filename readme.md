# seninja
![](pictures/screen.png)
This is a binary ninja plugin that implements a (quite inefficient) symbolic execution engine based only on z3. It is implemented as an emulator of LLIL instructions that builds and manipulates z3 formulas.

**NOTE**: The plugin is an early development stage (e.g., it lacks many LLIL instruction handlers, I'll add them eventually), so do not expect nothing special.

#### commands
- `seninja: start symbolic execution`: can be executed by right-clicking on an instruction. The command creates a symbolic state at the current address. the state's memory is (lazily) initialized with the data of the binary. Some registers and some stack memory locations are initialized using binaryninja's VSA. All the uninitialized registers and memory locations are considered symbolic. This new state becomes the active state (highlighted in green in the GUI).
- `seninja: step`: the command executes one (LLIL) instruction in the current active state. If the instruction is a branch, two states will be created. One of the two becomes the active state (green) while the other will be put in a deferred list (red in the GUI).
- `seninja: continue until branch`: the command executes the instructions until a branch is reached.
- `seninja: change current state`: can be executed by right-clicking on an instruction with a deferred state. The deferred states becomes the active state.

The current state is accessible through the python shell. Example:
```
>>> import seninja
>>> s = seninja.get_current_state()
>>> s.solver.satisfiable(extra_constraints=[s.regs.eax == 3])
```
the code will check the satisfiablity of `eax == 3` given the path constraint of the current state. Look at the code for memory read/write and other possible interactions with the state.

<!-- #### memory model
The memory model is fully symbolic (no concretization) and is based on the one of S2E (https://github.com/S2E) and KLEE (https://github.com/klee/klee):
- it uses the *theory of arrays* to model memory pages (whose size is tunable)
- if a symbolic address span multiple pages, it will create an ITE expression with a case for each (mapped) page

I'm planning to build other memory models and to improve the performance of this one ( that is quite inefficient and probably broken :) ) -->

#### version and dependencies
I tested it on binaryNinja Version 1.1.1689 Personal (with python 3)

Depends (heavily) on z3 (`pip3 install z3-solver`)
