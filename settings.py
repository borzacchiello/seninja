from binaryninja import Settings

Settings().register_group("seninja", "SENinja")
Settings().register_setting("seninja.memory.symb_address_mode", """
    {
        "title" : "Symbolic access mode",
        "type" : "string",
        "default" : "limit_pages",
        "description" : "Select the policy to use when a memory access from symbolic address occurs.",
        "enum": ["concretization", "limit_pages", "fully_symbolic"]
    }
    """)
Settings().register_setting("seninja.memory.limit_pages_limit", """
    {
        "title" : "Limit pages, page limit",
        "type" : "number",
        "default" : 3,
        "description" : "If the symbolic access policy is set to 'limit_pages', the maximum width of a symbolic access (in pages)."
    }
    """)
Settings().register_setting("seninja.memory.concretize_unconstrained", """
    {
        "title" : "Concretize unconstrained memory accesses",
        "type" : "boolean",
        "default" : true,
        "description" : "When a memory access on a unconstrained symbolic address occurs, allocate a new page and concretize the address to it."
    }
    """)
Settings().register_setting("seninja.memory.use_heuristic_find_base", """
    {
        "title" : "Use find-base heuristic on symbolic memory accesses",
        "type" : "boolean",
        "default" : true,
        "description" : "When a memory access on a symbolic address occurs, if the current policy impose concretization, use find-base heuristic to drive the concretization."
    }
    """)
Settings().register_setting("seninja.memory.check_unmapped", """
    {
        "title" : "Check unmapped symbolic memory accesses",
        "type" : "boolean",
        "default" : false,
        "description" : "Check if symbolic memory accesses can access unmapped memory pages. Performance may decrease."
    }
    """)
Settings().register_setting("seninja.memory.page_size", """
    {
        "title" : "Size of a memory page",
        "type" : "string",
        "default" : "4096",
        "description" : "Size (in bytes) of a memory page. It must be a power of 2."
    }
    """)

Settings().register_setting("seninja.stack_size", """
    {
        "title" : "Stack size (in pages)",
        "type" : "number",
        "default" : 4,
        "description" : "Number of pages allocated for the stack."
    }
    """)
Settings().register_setting("seninja.use_bn_jumptable_targets", """
    {
        "title" : "Use jump table targets computed by Binary Ninja",
        "type" : "boolean",
        "default" : true,
        "description" : "If true, the symbolic executor will use targets of jump tables computed by Binary Ninja."
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
        "description" : "If true, division by zero are checked. Performance may decrease."
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

Settings().register_setting("seninja.models.use_atox_slow_model", """
    {
        "title" : "Use atoX slow model",
        "type" : "boolean",
        "default" : true,
        "description" : "If true, atoX functions are modelled in a sound and complete (but slow) way."
    }
    """)
Settings().register_setting("seninja.models.max_malloc_size", """
    {
        "title" : "Maximum malloc size when concretized",
        "type" : "string",
        "default" : "4096",
        "description" : "Maximum value to which a symbolic malloc size can be concretized."
    }
    """)
Settings().register_setting("seninja.models.max_memcmp_size", """
    {
        "title" : "Maximum memcmp size when concretized",
        "type" : "string",
        "default" : "4096",
        "description" : "Maximum value to which a symbolic memcmp size can be concretized."
    }
    """)
Settings().register_setting("seninja.models.max_memcpy_size", """
    {
        "title" : "Maximum memcpy size when concretized",
        "type" : "string",
        "default" : "4096",
        "description" : "Maximum value to which a symbolic memcpy size can be concretized."
    }
    """)
Settings().register_setting("seninja.models.max_size_symb_string", """
    {
        "title" : "Maximum length of symbolic string",
        "type" : "number",
        "default" : 30,
        "description" : "Maximum length of a string with symbolic characters."
    }
    """)

Settings().register_setting("seninja.init_reg_mem_with_zero", """
    {
        "title" : "Set uninitialized registers and memory to zero",
        "type" : "boolean",
        "default" : false,
        "description" : "If true, memory and registers are inizialized with zero. Otherwise, with symbols."
    }
""")
