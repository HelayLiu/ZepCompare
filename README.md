# ZepCompare
## Overview
This repository is the artifact of the paper "Demystifying OpenZeppelin's Own Vulnerabilities and Analyzing Their Propagation in Smart Contracts". ZepCompare is a tool for detecting OpenZeppelin’s own vulnerabilities and analyzing their propagation in third-party smart contracts.
## How to use
The code of ZepCompare are in `code`, and the groundtruth dataset is in `datasets/groundtruth`, the addresses of the large scale experiment are in `datasets/large_size`

To run ZepCompare:

1. Install dependency:
```
pip install -r requirement.txt
```

2. run voliation_detection/detection_main.py

## License
This project is released under the MIT License.

## Citation
Please cite the paper as follows if you use the data or code from ZepCompare:
```
@inproceedings{liu2025zepcompare,
      title={{Demystifying OpenZeppelin's Own Vulnerabilities and Analyzing Their Propagation in Smart Contracts}}, 
      author={Liu, Han and Wu, Daoyuan and Sun, Yuqiang and Wang, Shuai and Liu, Yang and Yixiang, Chen},
      booktitle={Proc. IEEE/ACM Automated Software Engineering (ASE)},
      year={2025}
}
```
