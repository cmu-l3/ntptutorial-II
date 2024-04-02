# From https://github.com/zhangir-azerbayev/repl/blob/master/pylean/pylean/__init__.py
import pexpect
import json

import os

class LeanServer:
    def __init__(self, path_to_repl):
        self.proc = pexpect.spawn(
            "lake env lean --run REPL/Main.lean", cwd=path_to_repl, encoding="utf-8",
        )

    def run_code(self, code, env=None, verbose=False):
        if env:
            command = (
                json.dumps(dict(cmd=code, env=env))
            )  
        else:
            command = (
                '{ "cmd" : "' + repr(code)[1:-1] + '" }'
            )  

        if verbose:
            print(command)
        self.proc.sendline(command)
        self.proc.expect_exact(command + "\r\n")
        self.proc.sendline()
        self.proc.expect_exact("\r\n")
        try:
            index = self.proc.expect('env": \d+\}', timeout=300)
            output = self.proc.before + self.proc.match.group()
            if verbose: 
                print(output)
            return json.loads(output)
        except pexpect.exceptions.TIMEOUT:
            raise pexpect.exceptions.TIMEOUT

