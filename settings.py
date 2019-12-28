from binaryninja import Settings

Settings().register_group("seninja", "SENinja")
Settings().register_setting("seninja.symb_address_mode", """
    {
        "title" : "Symbolic access mode",
        "type" : "string",
        "default" : "limit_pages",
        "description" : "Select the policy to use when a memory access form symbolic memory occurs.",
        "enum": ["concretization", "limit_pages", "full_symbolic"]
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
