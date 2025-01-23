import os
import re
from collections import deque
from tqdm import tqdm
def topological_sort(edges):
    """
    Perform topological sort on a graph represented as a dictionary.
    Correctly handle the removal of nodes and updating the indegree of adjacent nodes.
    """
    # Create a dictionary to count the indegrees of each node
    indegree = {node: 0 for node in edges}
    for node in edges:
        for neighbor in edges[node]:
            indegree[neighbor] = indegree.get(neighbor, 0) + 1

    # Initialize a queue with nodes having indegree 0
    queue = deque([node for node in indegree if indegree[node] == 0])

    sorted_order = []
    while queue:
        node = queue.popleft()
        sorted_order.append(node)

        # For each neighbor, decrease the indegree and add to queue if indegree becomes 0
        for neighbor in edges.pop(node, []):
            indegree[neighbor] -= 1
            if indegree[neighbor] == 0:
                queue.append(neighbor)

    # If all nodes are processed, return the sorted order, else graph has a cycle
    # if len(sorted_order) == len(indegree):
    return sorted_order
    # else:
    #     return "A topological sort is not possible (the graph is not a DAG)."
def conbine2one_file(root_path):
    file_name=root_path.split('/')[-1]
    file_name=file_name.split('openzeppelin-contracts-')[-1]
    files_content={}
    cou_version={}
    dependency={}
    root_path=os.path.join(root_path,'contracts')
    for root, dirs, files in os.walk(root_path):
        for file in files:
            if '/mocks' in root:
                continue
            if file.endswith('.sol'):
                if file in files_content and files_content[file]!='':
                    continue
                if file not in dependency:
                    dependency[file]=[]
                file_path=os.path.join(root,file)
                with open(file_path,'r') as f:
                    content=f.read()

                    version=re.findall(r'pragma solidity (.*?);',content)[0]
                    if version not in cou_version:
                        if version.startswith('^'):
                            version_num=version[1:]
                        else:
                            version_num=version
                        if ' ' in version_num:
                            version_num=version_num.split(' ')[0]
                        if '^' in version_num:
                            version_num=version_num.split('^')[0]
                        if '>=' in version_num:
                            version_num=version_num.split('>=')[-1]
                        if '<' in version_num:
                            version_num=version_num.split('<')[-1]
                        if '<=' in version_num:
                            version_num=version_num.split('<=')[-1]
                        if '>' in version_num:
                            version_num=version_num.split('>')[-1]
                        if version_num.startswith('0.'):
                            version_num=version_num[2:]
                        try:
                            version_num=float(version_num)
                        except:
                            version_num=1
                        cou_version[version]=version_num
                    filename_pattern = r'import\s+(?:\{[^\}]*\}\s+as\s+[^\s]+\s+|\{[^\}]*\}\s+|).*\/([^\/]+\.sol)("|\');'

                    # Extracting the file names using the adjusted regex pattern
                    extracted_filenames = re.findall(filename_pattern, content)
                    extracted_filenames =[ filename[0] for filename in extracted_filenames]
                    extracted_filenames=set(extracted_filenames)    
                    if extracted_filenames:
                        for extracted_filename in extracted_filenames:
                            if extracted_filename not in dependency:
                                dependency[extracted_filename]=[]
                            if extracted_filename!=file:
                                dependency[extracted_filename].append(file)
                    content_without_version_import=[]
                    content=content.split('\n')
                    for i in range(len(content)):
                        if not content[i].startswith('pragma solidity') and not content[i].startswith('import') and not content[i]=='' and not content[i].startswith('//'):
                            content_without_version_import.extend(content[i:])
                            break
                    content_without_version_import='\n'.join(content_without_version_import)
                    files_content[file]=content_without_version_import
    final_version=max(cou_version,key=cou_version.get)
    if ' ' in final_version:
        final_version=final_version.split(' ')[0]
    if '>=' in final_version:
        final_version=final_version.split('>=')[-1]
    if '<' in final_version:
        final_version=final_version.split('<')[-1]
    if '<=' in final_version:
        final_version=final_version.split('<=')[-1]
    if '>' in final_version:
        final_version=final_version.split('>')[-1]                     
    final_file=f'''// SPDX-License-Identifier: MIT
pragma solidity {final_version};

'''
    
    file_queue=topological_sort(dependency)
    for file in file_queue:
        final_file+=files_content[file]
        final_file+='\n'
    if final_version.startswith('^'):
        final_version=final_version[1:]
    with open(os.path.join('./fact_extaction/resources',f'{file_name}@{final_version}.sol'),'w') as f:
        f.write(final_file)

if __name__=='__main__':
    path='./openzeppelin'
    for ver in tqdm(os.listdir(path)):
        if ver.startswith('openzeppelin-contracts-1.2.0'):
            try:
                conbine2one_file(os.path.join(path,ver))
            except Exception as e:
                print(e)
                print(ver)