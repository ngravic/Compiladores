import os
import subprocess

def getAllTigerFiles(folder):
        files = []
        for r, _, f in os.walk(folder):
            for file in f:
                if '.tig' in file:
                    files.append(os.path.join(r, file))        
        return files

def runTest(file):
    TIGER_PATH = "../tiger/"
    p = subprocess.Popen([TIGER_PATH, file], stdout=subprocess.PIPE, shell=True)
    (out, err) = p.communicate()
    p.wait()
    return out