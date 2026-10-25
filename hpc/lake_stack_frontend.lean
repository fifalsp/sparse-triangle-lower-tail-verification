-- Resource-control entry point only; not part of the mathematical source tree.
-- Running through `lean -s... --run` configures Lake's own runtime stack.
import Lake.DSL
import Lake.CLI.Main

def main (args : List String) : IO UInt32 := Lake.cli args
