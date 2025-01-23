import sys
from pathlib import Path
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))
from configs import *
import os
import subprocess
from tqdm import tqdm
if __name__=='__main__':
    version_list=set()
    for key in version_pairs:
        version_list.add(key)
        version_list.add(version_pairs[key])
    for version in tqdm(version_list):
        try:
            path=os.path.join(zeppelin_path,f'openzeppelin-contracts-{version}')
            url=f"https://github.com/OpenZeppelin/openzeppelin-contracts/archive/refs/tags/v{version}.tar.gz"
            res=subprocess.run(f"wget {url} -O {version}.tar.gz",shell=True,cwd=zeppelin_path,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            res.check_returncode()
            subprocess.run(f"tar -zxvf {version}.tar.gz",shell=True,cwd=zeppelin_path,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            subprocess.run("npx hardhat compile",shell=True,cwd=path,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        except:
            print(f'error in {version}')
        
        
