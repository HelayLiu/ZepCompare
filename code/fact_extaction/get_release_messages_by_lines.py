import requests
import re
import json
from openai import OpenAI
from tqdm import tqdm
OPENAI_API_KEY = "sk-1"
def judge_by_GPT(line):
    role_content=f"""Now you are a smart contracts security audit expert, I give you a description about a change 
    of the smart contract code, please help me judge whether the change is security related (e.g., fix vunlerabilities)
    instead of other types of changes (e.g., add functions). Please output [Yes/No] to represent the description is 
    security related (Yes) or not (No)"""
    try:
        client= OpenAI(api_key=OPENAI_API_KEY)
        response = client.chat.completions.create(
                            model="gpt-3.5-turbo-0125",
                            messages=[
                                {"role": "system", "content": role_content},
                                {"role": "user", "content": f"The description is {line}"},
                            ],
                            temperature = 0,
                        )
    except Exception as e:
        print('Error in response')
    return response.choices[0].message.content
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
            for line in tqdm(lines):
                #先用\n分割，再找出前面部分，在找网址
                if len(line)<5:
                    continue
                try:
                    judge_related=judge_by_GPT(line)
                    # judge_related='Yes'
                except Exception as e:
                    print('Error in judge')
                if judge_related!='Yes':
                    continue
                # pattern = r'- `([^`]+)`: (.*)\. (\(\[#\d+\])(\s*)(\(https:\/\/github\.com\/OpenZeppelin\/openzeppelin-contracts\/pull\/^\d{1,4}$\))'
                pattern=r'(\(https:\/\/github\.com\/OpenZeppelin\/.*?\))'
                matches = re.finditer(pattern, line)
                urls=[] 
                for match in matches:
                    url = match.group(1)
                    urls.append(url[1:-1])
                if urls==[]:
                    pattern=r'(#\b\d{3,4}\b)'
                    matches = re.finditer(pattern, line)
                    for match in matches:
                        url = match.group(1)
                        urls.append('https://github.com/OpenZeppelin/openzeppelin-contracts/pull/'+url[1:-1])
                des[line]=urls
            # print(f"Release: {release['name']}")
            # print(f"Tag: {release['tag_name']}")
            # print(f"Date: {release['published_at']}")
            # print(f"Description: {release['body']}")
            # print("-" * 40)
            res[version]=des
    else:
        print(f"Failed to fetch releases. Status code: {response.status_code}")
    with open('version_description1.json','w') as f:
        json.dump(res,f,indent=4)

get_releases('OpenZeppelin', 'openzeppelin-contracts')
