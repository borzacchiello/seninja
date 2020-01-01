from binaryninja import Settings

# https://github.com/Vector35/binaryninja-api/blob/7971d55486180e07a8bd3a0741bac7b03b6fe460/examples/triage/triage.cpp

Settings().register_group("seninja", "SENinja")
Settings().register_setting("seninja.mem.symb_address_mode", """
    {
        "title" : "Symbolic access mode",
        "type" : "string",
        "default" : "limit_pages",
        "description" : "Select the policy to use when a memory access from symbolic address occurs.",
        "enum": ["concretization", "limit_pages", "fully_symbolic"]
    }
    """)
Settings().register_setting("seninja.mem.limit_pages_limit", """
    {
        "title" : "Limit pages, page limit",
        "type" : "number",
        "default" : 3,
        "description" : "If the symbolic access policy is set to 'limit_pages', the maximum width of a symbolic access (in pages)."
    }
    """)
Settings().register_setting("seninja.mem.concretize_unconstrained", """
    {
        "title" : "Concretize unconstrained memory accesses",
        "type" : "boolean",
        "default" : true,
        "description" : "When a memory access on a unconstrained symbolic address occurs, allocate a new page and concretize the address to it."
    }
    """)
Settings().register_setting("seninja.mem.use_heuristic_find_base", """
    {
        "title" : "Use find-base heuristic on symbolic memory accesses",
        "type" : "boolean",
        "default" : true,
        "description" : "When a memory access on a symbolic address occurs, if the current policy impose concretization, use find-base heuristic to drive the concretization."
    }
    """)
Settings().register_setting("seninja.save_unsat", """
    {
        "title" : "Save unsat states",
        "type" : "boolean",
        "default" : false,
        "description" : "Save unsatisfiable states. If True, performance will decrease drastically."
    }
    """)
Settings().register_setting("seninja.single_llil_step", """
    {
        "title" : "Single LLIL step",
        "type" : "boolean",
        "default" : false,
        "description" : "If true, a single step executes only one LLIL instruction, instead of an assembly instruction."
    }
    """)
Settings().register_setting("seninja.check_division_by_zero", """
    {
        "title" : "Check division by zero",
        "type" : "boolean",
        "default" : false,
        "description" : "If true, division by zero are checked. Performance will decrease."
    }
    """)
Settings().register_setting("seninja.dont_use_special_handlers", """
    {
        "title" : "Do not use special handlers",
        "type" : "boolean",
        "default" : false,
        "description" : "If true, architecture-specific handlers will not be used."
    }
    """)
Settings().register_setting("seninja.use_atox_slow_model", """
    {
        "title" : "Use atoX slow model",
        "type" : "boolean",
        "default" : true,
        "description" : "If true, atoX functions are modelled in a sound and complete (but slow) way."
    }
    """)
