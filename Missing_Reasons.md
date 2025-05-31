Among the 35 security bugs, 7 were missed by ZepCompare, we analyze the reasons in detailed for these missed detections as follows:

- The detection granularity in ZepCompare is larger than the issues in the ground-truth dataset.
In ZepCompare, we narrow the granularity of the extracted fact to the line level.
However, some of OpenZeppelin's code is highly concise, with multiple checks occurring within a single line.
For example, in the OpenZeppelin vulnerability CVE-2022-31172, the issue arises because `abi.decode` reverts if the raw bytes data overflows the target type, requiring `bytes4` to be cast to `bytes32`.
This line also contains other checks, such as `success \&\& result.length >= 32`.
 Our method, which evaluates the entire line, can misinterpret the relevant facts.
Consequently, if the target function addresses the issue elsewhere in the code, like the `isValidSignature` function in project 10 from the Web3Bugs dataset, our structured matching may fail.
If we reduce the granularity further to individual checks or specific values, it would lead to excessive false positives (e.g., `abi.decode(returndata, (bytes4))` appearing frequently without being relevant).
To balance false positives and detection accuracy, we set the extraction granularity at the line level.

- Another reason for missed detections is matching failures.
Our detection process involves two stages: first, using function signatures to identify potential issues, followed by structured matching.
Although we use a lenient policy for signature matching (e.g., allowing low function name similarity and parameter additions), some functions may still be missed, such as when parameter names are modified.
This is inevitable due to the large number of functions in each contract and statements within each function.
Direct matching without function signatures would be inefficient, so we optimize time efficiency using signatures and maximize detection with flexible matching.
