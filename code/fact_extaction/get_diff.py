import requests
import json
import copy
from tqdm import tqdm
# Pull Request API URL
def get_diff(url):
    url=url.replace('https://github.com/','https://api.github.com/repos/')
    url=url.replace('/pull/','/pulls/')
    token = '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'
    # HTTP请求头
    headers = {
        'Authorization': f'token {token}',
        'Accept': 'application/vnd.github.v3.diff',
    }

    # 发送请求并获取响应
    response = requests.get(url, headers=headers)

    # 检查响应状态码
    if response.status_code == 200:
        lines=response.text.split('\n')
        is_sol=False
        add_line=[]
        del_line=[]
        for line in lines:
            if line.startswith('diff'):
                if '.sol' in line:
                    is_sol=True
                else:
                    is_sol=False
            if is_sol:
                if line.startswith('+') and line!='+' and not line.startswith('+++') and not line.startswith('+import') and '// ' not in line and not line.startswith('+pragma') and '/**' not in line and '':
                    add_line.append(line[1:])
                elif line.startswith('-') and line!='-' and not line.startswith('---') and not line.startswith('-import') and '// ' not in line and not line.startswith('-pragma'):
                    del_line.append(line[1:])             
        diff={'add':add_line,'del':del_line}
        return diff
    else:
        print(f'Failed to get diff file: {response.status_code}')
        print(url)
        return {'add':[],'del':[]}
if __name__=='__main__':
    with open('./fact_extaction/version_description1.json', 'r') as f:
        versions=json.load(f)
        versions_cp=copy.deepcopy(versions)
        for version in tqdm(versions):
            for changes in tqdm(versions[version]):
                for change in versions[version][changes]:
                    if '/pull/' in change:
                        diff=get_diff(change)
                        versions_cp[version][changes]=[{change:diff} if x==change else x for x in versions_cp[version][changes]]
    with open('./fact_extaction/version_with_diff.json', 'w') as f:
        json.dump(versions_cp,f,indent=4)