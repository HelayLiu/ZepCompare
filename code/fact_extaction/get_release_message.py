import requests
import re
import json
def get_releases(owner, repo):
    url = f"https://api.github.com/repos/{owner}/{repo}/releases"
    response = requests.get(url)
    res={}
    if response.status_code == 200:
        releases = response.json()
        for release in releases:
            version=release['tag_name'].replace('v','')
            body=release['body']
            #先用\n分割，再找出前面部分，在找网址
            # pattern = r'- `([^`]+)`: (.*)\. (\(\[#\d+\])(\s*)(\(https:\/\/github\.com\/OpenZeppelin\/openzeppelin-contracts\/pull\/^\d{1,4}$\))'
            pattern=r'- (.*)\.\(((\[#\d+\])\s*\((https:\/\/github\.com\/OpenZeppelin\/openzeppelin-contracts\/pull\/\d{1,4})\)(\s|,)*)+'
            matches = re.finditer(pattern, body)
            des={}
            for match in matches:
                component = match.group(1)
                description = match.group(2)
                url = match.group(3)
                combined_sentence = f"{component}: {description}"
                des[combined_sentence]=url
            # print(f"Release: {release['name']}")
            # print(f"Tag: {release['tag_name']}")
            # print(f"Date: {release['published_at']}")
            # print(f"Description: {release['body']}")
            # print("-" * 40)
            res[version]=des
    else:
        print(f"Failed to fetch releases. Status code: {response.status_code}")
    with open('version_description.json','w') as f:
        json.dump(res,f,indent=4)

get_releases('OpenZeppelin', 'openzeppelin-contracts')
