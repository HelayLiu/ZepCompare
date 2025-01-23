import sys
from pathlib import Path
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))
import requests
import re
import json
from gpt_validation import GPT_judge_desc, GPT_judge_desc_with_code, GPT_judge_code_sec_related
from tqdm import tqdm
debug_no_GPT=False
def get_releases(owner, repo):
    url = f"https://api.github.com/repos/{owner}/{repo}/releases"
    response = requests.get(url,{'per_page':100})
    res={}
    if response.status_code == 200:
        releases = response.json()
        for release in tqdm(releases):
            des={}
            version=release['tag_name'].replace('v','')
            body=release['body']
            lines=body.split('\n')
            all_codes=[]
            for line in tqdm(lines):
                #先用\n分割，再找出前面部分，在找网址
                if len(line)<5:
                    continue
                try:
                    if debug_no_GPT:
                        judge_related='Yes'
                    else:
                        judge_related=GPT_judge_desc(line)
                    # judge_related='Yes'
                    if 'YES' not in judge_related:
                        continue
                except Exception as e:
                    print('Error in judge')

                # pattern = r'- `([^`]+)`: (.*)\. (\(\[#\d+\])(\s*)(\(https:\/\/github\.com\/OpenZeppelin\/openzeppelin-contracts\/pull\/^\d{1,4}$\))'
                pattern=r'(\(https:\/\/github\.com\/OpenZeppelin\/.*?\))'
                matches = re.finditer(pattern, line)
                urls=[] 
                for match in matches:
                    url = match.group(1)
                    codes_res={}
                    url_re=url[1:-1]
                    codes=get_diff(url_re)
                    for code_name,code in codes:
                        code_res=True
                        if not code_desc_related_judge(line, code):
                            code_res=False
                            codes_res[code]=(code_res,code_name)
                            continue
                        if not code_judge(code):
                            code_res=False
                            codes_res[code]=(code_res,code_name)
                            continue
                        codes_res[code]=(code_res,code_name)
                        all_codes.extend(code.split('\n'))
                    urls.append({url_re:codes_res})
                if urls==[]:
                    pattern=r'(#\b\d{3,4}\b)'
                    matches = re.finditer(pattern, line)
                    for match in matches:
                        url = match.group(1)
                        codes_res={}
                        url_re='https://github.com/OpenZeppelin/openzeppelin-contracts/pull/'+url[1:]
                        codes=get_diff(url_re)
                        for code_name,code in codes:
                            code_res=True
                            if not code_desc_related_judge(line, code):
                                code_res=False
                                codes_res[code]=(code_res,code_name)
                                continue
                            if not code_judge(code):
                                code_res=False
                                codes_res[code]=(code_res,code_name)
                                continue
                            codes_res[code]=(code_res,code_name)
                            all_codes.extend(code.split('\n'))
                        urls.append({url_re:codes_res})
                des[line]=urls
            res[version]=des
    else:
        print(f"Failed to fetch releases. Status code: {response.status_code}")
    return res

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
    codes=[]
    # 检查响应状态码
    if response.status_code == 200:
        lines=response.text.split('\n')
        is_sol=False
        code=[]
        start_file=False
        code_name=''
        for line in lines:
            if line.startswith('diff'):
                if '.sol' in line:
                    is_sol=True
                    code_name=line.split('.sol')[0]
                    code_name=code_name.split('/')[-1]
                    continue
                else:
                    is_sol=False
            if is_sol:
                if line.startswith('@@') or line.startswith('index') or line.startswith('---') or line.startswith('+++'):
                    start_file=True
                    code_str='\n'.join(code)
                    if code_str!='':
                        codes.append((code_name,code_str))
                    code=[]
                    continue
                elif start_file:
                    code.append(line)
        if code!=[]:
            code_str='\n'.join(code) 
            codes.append((code_name,code_str))         
        return codes
    else:
        print(f'Failed to get diff file: {response.status_code}')
        print(url)
        return ''

def code_desc_related_judge(description, code):
    try:
        if debug_no_GPT:
            judge_related='Yes'
        else:
            judge_related=GPT_judge_desc_with_code(description, code)
        if 'YES' not in judge_related:
            return False
    except Exception as e:
        print('Error in judge')

    return True

def code_judge(code):
    try:
        if debug_no_GPT:
            judge_related='Yes'
        else:
            judge_related=GPT_judge_code_sec_related(code)

        if 'YES' not in judge_related:
            return False
    except Exception as e:
        print('Error in judge')
    return True


if __name__=='__main__':
    ver_descs=get_releases('OpenZeppelin', 'openzeppelin-contracts')
    with open('release4.json','w') as f:
        json.dump(ver_descs,f,indent=4)