from binaryninja import Settings

# https://github.com/Vector35/binaryninja-api/blob/7971d55486180e07a8bd3a0741bac7b03b6fe460/examples/triage/triage.cpp

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
