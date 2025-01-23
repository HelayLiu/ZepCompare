import requests
import re
import json
from openai import OpenAI
from tqdm import tqdm
OPENAI_API_KEY = "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"
def GPT_judge_desc(desc,model="gpt-4o-mini-2024-07-18"):
    role_content=f"""Now you are a smart contracts security audit expert, I give you a description about a change 
    of the smart contract code, please help me judge whether the change is security related (e.g., fix vunlerabilities)
    instead of other types of changes (e.g., add functions). Noted that if the code change is just convert the require statement to the if-revert statement,
    it is not security related.
    Please first output [YES] or [NO] to represent the description is security related (Yes) or not (No), then output the reason why you think so."""
    try:
        client= OpenAI(api_key=OPENAI_API_KEY)

        response = client.chat.completions.create(
                            model=model,
                            messages=[
                                {"role": "system", "content": role_content},
                                {"role": "user", "content": f'''The description is <desc> {desc} </desc>'''},
                            ],
                            temperature = 0,
                        )
    except Exception as e:
        print('Error in response')
    return response.choices[0].message.content

def GPT_judge_desc_with_code(desc, code,model="gpt-4o-mini-2024-07-18"):
    role_content=f"""Now you are a smart contracts security audit expert, I give you a description about a change 
    of the smart contract code and a code snippet, please help me judge whether the description and the code snippet
    are related. 
    Please first output [YES] or [NO] to represent the description and the code snippet are related (Yes) or 
    not (No), then output the reason why you think so."""
    try:
        client= OpenAI(api_key=OPENAI_API_KEY)
        response = client.chat.completions.create(
                            model=model,
                            messages=[
                                {"role": "system", "content": role_content},
                                {"role": "user", "content": f'''The description is <desc> {desc} </desc>.
                                 The code is <code>{code}</code>.'''},
                            ],
                            temperature = 0,
                        )
    except Exception as e:
        print('Error in response')
    return response.choices[0].message.content

def GPT_judge_code_sec_related(code,model="gpt-4o-mini-2024-07-18"):
    role_content=f"""Now you are a smart contracts security audit expert, I give you a code snippet about a change 
    in smart contract development activity, please help me judge whether the the code snippet is security related (e.g. fix a vunlerability)
    instead of other types of changes (e.g., add functions). Noted that if the code change is just convert the require statement to the if-revert statement,
    it is not security related.
    Please first output [YES] or [NO] to represent the code snippet are related (Yes) or not (No), then output the reason why you think so."""
    try:
        client= OpenAI(api_key=OPENAI_API_KEY)
        response = client.chat.completions.create(
                            model=model,
                            messages=[
                                {"role": "system", "content": role_content},
                                {"role": "user", "content": f'''The code is <code>{code}</code>.'''},
                            ],
                            temperature = 0,
                        )
    except Exception as e:
        print('Error in response')
    return response.choices[0].message.content


