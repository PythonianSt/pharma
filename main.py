import os, io, csv, json, base64, re, time, hmac, hashlib, secrets, html, uuid
from datetime import datetime
from zoneinfo import ZoneInfo
from functools import wraps

import requests
from cryptography.fernet import Fernet, InvalidToken
from flask import Flask, request, jsonify, render_template_string, session, redirect, url_for

app = Flask(__name__)
app.secret_key = os.environ.get("FLASK_SECRET_KEY", "CHANGE-ME-IN-VERCEL")
BKK = ZoneInfo("Asia/Bangkok")

# ---------- CONFIG ----------
GITHUB_OWNER = os.environ.get("GITHUB_OWNER", "")
GITHUB_REPO = os.environ.get("GITHUB_REPO", "")
GITHUB_BRANCH = os.environ.get("GITHUB_BRANCH", "main")
GITHUB_TOKEN = os.environ.get("GITHUB_TOKEN", "")
GITHUB_RX_CSV_PATH = os.environ.get("GITHUB_RX_CSV_PATH", "data/prescriptions.csv")

DOCTOR_PIN = os.environ.get("DOCTOR_PIN", "")
PHARMACIST_PIN = os.environ.get("PHARMACIST_PIN", "")
HN_HASH_SECRET = os.environ.get("HN_HASH_SECRET", "")
PATIENT_DATA_KEY = os.environ.get("PATIENT_DATA_KEY", "")
ICD10_CSV_PATH = os.environ.get("ICD10_CSV_PATH", "data/icd10.csv")

# ---------- ICD-10 ----------
KEYWORD_HINTS = {
    "cold / URI": ["J00", "J06", "common cold", "upper respiratory"],
    "pharyngitis": ["J02", "pharyngitis"],
    "tonsillitis": ["J03", "tonsillitis"],
    "influenza / ILI": ["J10", "J11", "influenza"],
    "COVID-19": ["U07", "COVID"],
    "cough": ["R05", "cough"],
    "fever": ["R50", "fever"],
    "allergic rhinitis": ["J30", "allergic rhinitis"],
    "sinusitis": ["J01", "sinusitis"],
    "otitis": ["H60", "H66", "otitis"],
    "conjunctivitis": ["H10", "B30", "conjunctivitis"],
    "diarrhea": ["A09", "K52", "diarrhea", "gastroenteritis"],
    "dyspepsia": ["K30", "dyspepsia"],
    "gastritis": ["K29", "gastritis"],
    "abdominal pain": ["R10", "abdominal pain"],
    "nausea / vomiting": ["R11", "nausea", "vomiting"],
    "constipation": ["K59.0", "constipation"],
    "headache": ["R51", "G44", "headache"],
    "migraine": ["G43", "migraine"],
    "dizziness": ["R42", "dizziness"],
    "syncope": ["R55", "syncope"],
    "strain": ["T14.6", "S39", "strain"],
    "sprain": ["T14.3", "S93", "sprain"],
    "myalgia": ["M79.1", "myalgia"],
    "back pain": ["M54", "back pain", "dorsalgia"],
    "neck pain": ["M54.2", "cervicalgia"],
    "shoulder pain": ["M25.51", "shoulder pain"],
    "knee pain": ["M25.56", "knee pain"],
    "ankle pain": ["M25.57", "ankle pain"],
    "wound / abrasion": ["S00","S10","S20","S30","S40","S50","S60","S70","S80","S90","abrasion","wound"],
    "contusion": ["contusion"],
    "rash": ["R21", "rash"],
    "dermatitis": ["L20", "L23", "L24", "L30", "dermatitis"],
    "urticaria": ["L50", "urticaria"],
    "tinea": ["B35", "tinea"],
    "cellulitis": ["L03", "cellulitis"],
    "abscess": ["L02", "abscess"],
    "herpes simplex": ["B00", "herpes simplex"],
    "herpes zoster": ["B02", "herpes zoster"],
    "dengue": ["A90", "A91", "dengue"],
    "hand-foot-mouth": ["B08.4", "hand foot mouth"],
    "UTI": ["N39.0", "urinary tract infection"],
    "dysuria": ["R30", "dysuria"],
    "STI": ["A50", "A51", "A54", "A56", "A60", "sexually transmitted"],
    "anxiety": ["F41", "anxiety"],
    "insomnia": ["G47.0", "insomnia"],
}

def load_icd10():
    path = os.path.join(os.path.dirname(__file__), ICD10_CSV_PATH)
    rows = []
    try:
        with open(path, "r", encoding="utf-8-sig", newline="") as f:
            for r in csv.DictReader(f):
                code = (r.get("code") or "").strip().upper()
                title = (r.get("title") or "").strip()
                keywords = (r.get("keywords") or "").strip()
                if code and title:
                    rows.append({"code": code, "title": title, "keywords": keywords})
    except FileNotFoundError:
        pass
    return rows

ICD10_ROWS = load_icd10()
ICD10_BY_CODE = {r["code"]: r for r in ICD10_ROWS}

def icd_lookup_exact(code):
    return ICD10_BY_CODE.get((code or "").strip().upper())

def icd_search(q="", hint="", limit=50):
    q = (q or "").strip().lower()
    hints = [str(x).lower() for x in KEYWORD_HINTS.get(hint, [])]
    scored = []
    for r in ICD10_ROWS:
        code = r["code"].lower()
        title = r["title"].lower()
        keys = r["keywords"].lower()
        hay = f"{code} {title} {keys}"
        score = 0
        if q:
            if code == q: score += 100
            elif code.startswith(q): score += 60
            if q in title: score += 50
            if q in keys: score += 35
            if q not in hay: continue
        if hints:
            hs = max([40 if code.startswith(h) else 25 if h in hay else 0 for h in hints] or [0])
            score += hs
            if not q and hs == 0: continue
        scored.append((score, r))
    scored.sort(key=lambda x: (-x[0], x[1]["code"]))
    return [r for _, r in scored[:limit]]

# ---------- DRUG MASTER จากโปรแกรมห้องยาเดิม ----------
MED_LIST = {'amoxicillin': 'Amoxicillin 500 mg', 'dicloxacillin 250': 'Dicloxacillin 250 mg', 'dicloxacillin 500': 'Dicloxacillin 500 mg', 'dicloxacillin': 'Dicloxacillin 500 mg', 'doxycycline': 'Doxycycline 100 mg', 'clindamycin': 'Clindamycin 300 mg', 'amoxicillin clavulanate': 'Amoxicillin + clavulanate 1 g', 'amoxicillin + clavulanate': 'Amoxicillin + clavulanate 1 g', 'augmentin': 'Amoxicillin + clavulanate 1 g', 'metronidazole': 'Metronidazole 400 mg', 'roxithromycin': 'Roxithromycin 150 mg', 'norfloxacin': 'Norfloxacin 400 mg', 'ofloxacin': 'Ofloxacin 200 mg', 'ciprofloxacin': 'Ciprofloxacin 500 mg', 'azithromycin': 'Azithromycin 250 mg', 'acyclovir': 'Acyclovir 400 mg', 'acyclovir cream': 'Acyclovir cream 1 g', 'itraconazole': 'Itraconazole 100 mg', 'antacid': 'Al750mg + Mg 300mg (Antacid) susp.', 'aluminium magnesium': 'Al750mg + Mg 300mg (Antacid) susp.', 'simeticone': 'Simeticone 80 mg', 'simethicone': 'Simeticone 80 mg', 'domperidone': 'Domperidone 10 mg', 'metoclopramide': 'Metoclopramide 10 mg', 'hyoscine': 'Hyoscine 10 mg', 'dicyclomine': 'Dicyclomine 10 mg + simethicone 100 mg', 'omeprazole': 'Omeprazole 20 mg', 'ors': 'ORS', 'oral rehydration': 'ORS', 'activated charcoal': 'Activated charcoal 260 mg', 'charcoal': 'Activated charcoal 260 mg', 'magnesium hydroxide': 'Magnesium hydroxide (MOM) susp.', 'mom': 'Magnesium hydroxide (MOM) susp.', 'senna': 'Senna', 'diosmin': 'Diosmin + Hesperidine', 'hesperidine': 'Diosmin + Hesperidine', 'doproct': 'Doproct suppo', 'cpm': 'CPM 4 mg', 'chlorpheniramine': 'CPM 4 mg', 'hydroxyzine': 'Hydroxyzine 10 mg', 'cetirizine': 'Cetirizine 10 mg', 'loratadine': 'Loratadine 10 mg', 'prednisolone': 'Prednisolone 5 mg', 'salbutamol': 'Salbutamol 2 mg', 'nasotapp': 'Nasotapp (Bromphe4 + Phenyl10)', 'nss syringe': 'NSS 0.9% + syringe 20 mL', 'inhalex': 'Inhalex Forte (Ipratropium + Fenoterol)', 'salbutamol neb': 'Salbutamol sulfate 2.5 mg/2.5 ml', 'dextromethorphan': 'Dextromethorphan 15 mg', 'brown mixture': 'Brown Mixture/Mist tussis', 'mist tussis': 'Brown Mixture/Mist tussis', 'acetylcysteine': 'Acetylcysteine 200 mg', 'nac': 'Acetylcysteine 200 mg', 'bromhexine': 'Bromhexine 8 mg', 'มะขามป้อม': 'ยาน้ำมะขามป้อม', 'มะแว้ง': 'มะแว้งอม', 'paracetamol': 'Paracetamol 500 mg', 'acetaminophen': 'Paracetamol 500 mg', 'diclofenac': 'Diclofenac 25 mg', 'ibuprofen': 'Ibuprofen 400 mg', 'naproxen': 'Naproxen 250 mg', 'mefenamic': 'Mefenamic acid 500 mg', 'aspirin 300': 'Aspirin 300 mg', 'aspirin': 'Aspirin 300 mg', 'norgesic': 'สูตร Norgesic', 'tolperisone': 'Tolperisone 50 mg', 'tramadol': 'Tramadol 50 mg', 'celecoxib': 'Celecoxib 200 mg', 'balm': 'Balm ทานวด', 'diclofenac gel': 'Diclofenac gel', 'gabapentin': 'Gabapentin 300 mg', 'hista oph': 'Hista-oph', 'chloramphenicol eye': 'Chloramphenicol eye drop', 'poly oph': 'Poly-oph', 'terramycin': 'Terramycin ointment', 'artificial tear': 'น้ำตาเทียม (Opsil tear, lac oph)', 'opsil': 'น้ำตาเทียม (Opsil tear, lac oph)', 'dewax': 'Dewax ear drop', 'tobramycin': 'Tobramycin 0.3% eye drop 5 ml', 'dex oph': 'สูตร Dex-oph', 'dimenhydrinate': 'Dimenhydrinate 50 mg', 'cinnarizine': 'Cinnarizine 25 mg', 'betahistine': 'Betahistine 6 mg', 'amitriptyline': 'Amitriptyline 10 mg', 'lorazepam': 'Lorazepam 0.5 / 1 mg', 'sertraline': 'Sertraline 50 mg', 'vitamin b complex': 'Vitamin B complex', 'vitamin b1': 'Vitamin B1-6-12', 'vitamin c': 'Vitamin C 50 mg', 'folic acid': 'Folic acid 5 mg', 'multivitamin': 'MultiVitamin', 'ferrous': 'Ferrous fumarate 200 mg', 'triamcinolone oral': 'Triamcinolone oral paste', 'ta lotion': 'TA 0.1% lotion', 'ta cream': 'TA 0.1% cream', 'ta 0.02': 'TA 0.02% cream', 'betamethasone': 'Betamet val 0.1% cream', 'clobetasol': 'Clobetasol 0.05% cream', 'calamine': 'Calamine lotion', 'clotrimazole': 'Clotrimazole cream', 'mupirocin': 'Mupirocin 2% ointment', 'salicylic': 'Con Con (salicylic acid)', 'norethisterone': 'Norethisterone 5 mg', 'metformin': 'Metformin 500 mg', 'amlodipine 5': 'Amlodipine 5 mg', 'amlodipine 10': 'Amlodipine 10 mg', 'amlodipine': 'Amlodipine 5 mg', 'atenolol': 'Atenolol 50 mg', 'enalapril 5': 'Enalapril 5 mg', 'enalapril 20': 'Enalapril 20 mg', 'enalapril': 'Enalapril 5 mg', 'simvastatin 10': 'Simvastatin 10 mg', 'simvastatin 20': 'Simvastatin 20 mg', 'simvastatin': 'Simvastatin 10 mg', 'propranolol': 'Propanolol 10 mg', 'propanolol': 'Propanolol 10 mg', 'losartan': 'Losartan 50 mg', 'aspirin 81': 'Aspirin 81 mg', 'adrenaline': 'Adrenaline 1 mg/ml (HAD)', 'ceftriaxone': 'Ceftriaxone 1 g', 'lincomycin': 'Lincomycin 300 mg/2ml', 'lidocaine': 'Lidocaine HCl inj. 2% w/v 2 mL', 'nss 100': 'NSS 0.9% sodium chloride inj. 100 ml', 'nss 500': 'NSS 0.9% sodium chloride inj. 500 ml', 'nss 1000': 'NSS 0.9% sodium chloride inj. 1000 ml', 'd5w': 'D5W 5% dextrose in water inj. 100 ml', 'acetate ringer': "Acetate ringer's injection 1000 ml", 'd-5-1/2': 'D-5-1/2 saline inj 1000 mL'}
MED_OPTIONS = sorted(set(MED_LIST.values()))

DEFAULT_SIG = {
    "Paracetamol 500 mg":"1 tab q6h prn pain/fever",
    "Ibuprofen 400 mg":"1 tab tid pc prn pain",
    "Diclofenac 25 mg":"1 tab tid pc prn pain",
    "Naproxen 250 mg":"1 tab bid pc prn pain",
    "Mefenamic acid 500 mg":"1 tab tid pc prn pain",
    "Celecoxib 200 mg":"1 cap od pc prn pain",
    "CPM 4 mg":"1 tab tid pc",
    "Cetirizine 10 mg":"1 tab od hs",
    "Loratadine 10 mg":"1 tab od",
    "Hydroxyzine 10 mg":"1 tab hs",
    "Dextromethorphan 15 mg":"1 tab tid prn cough",
    "Bromhexine 8 mg":"1 tab tid pc",
    "Acetylcysteine 200 mg":"1 sachet tid pc",
    "Omeprazole 20 mg":"1 cap od ac",
    "Hyoscine 10 mg":"1 tab tid ac prn abdominal-pain",
    "Domperidone 10 mg":"1 tab tid ac prn nausea",
    "Simeticone 80 mg":"1 tab tid pc prn bloating",
    "ORS":"1 sachet after-loose-stool",
    "Amoxicillin 500 mg":"1 cap tid pc",
    "Dicloxacillin 250 mg":"1 cap qid ac",
    "Doxycycline 100 mg":"1 cap bid pc",
    "Azithromycin 250 mg":"2 tab od pc",
    "Metronidazole 400 mg":"1 tab tid pc",
    "Acyclovir 400 mg":"1 tab 5times/day",
    "Prednisolone 5 mg":"1 tab tid pc",
    "Salbutamol 2 mg":"1 tab tid pc",
    "Gabapentin 300 mg":"1 cap hs",
    "Clotrimazole cream":"apply bid",
    "Mupirocin 2% ointment":"apply tid",
    "Calamine lotion":"apply tid prn itch",
}

def norm_text(x):
    return re.sub(r"[^a-z0-9ก-๙+/.-]+", " ", str(x).lower()).strip()

def find_med_in_stock(med_name):
    text = norm_text(med_name)
    if not text:
        return None
    for item in MED_OPTIONS:
        ni = norm_text(item)
        if ni in text or text in ni:
            return item
    for key in sorted(MED_LIST.keys(), key=len, reverse=True):
        if key in text:
            return MED_LIST[key]
    return None

# ---------- SIG ----------
FREQ = {
    "od":"วันละ 1 ครั้ง","bid":"วันละ 2 ครั้ง","tid":"วันละ 3 ครั้ง","qid":"วันละ 4 ครั้ง",
    "hs":"ก่อนนอน","q4h":"ทุก 4 ชั่วโมง","q6h":"ทุก 6 ชั่วโมง","q8h":"ทุก 8 ชั่วโมง",
    "q12h":"ทุก 12 ชั่วโมง","5times/day":"วันละ 5 ครั้ง"
}
MEAL = {"ac":"ก่อนอาหาร","pc":"หลังอาหาร"}
PRN = {
    "pain":"เมื่อมีอาการปวด","fever":"เมื่อมีไข้","pain/fever":"เมื่อมีอาการปวดหรือมีไข้",
    "cough":"เมื่อมีอาการไอ","nausea":"เมื่อมีอาการคลื่นไส้/อาเจียน","itch":"เมื่อมีอาการคัน",
    "bloating":"เมื่อมีอาการท้องอืด","abdominal-pain":"เมื่อมีอาการปวดท้อง"
}
FORMS = {"tab":"เม็ด","cap":"แคปซูล","sachet":"ซอง","ml":"มล.","puff":"พัฟ"}

def translate_sig(raw):
    s = re.sub(r"\s+", " ", (raw or "").strip().lower())
    if not s:
        return "", ["ยังไม่ได้ระบุ SIG"]
    if s == "1 sachet after-loose-stool":
        return "ครั้งละ 1 ซอง หลังถ่ายเหลวแต่ละครั้ง", []
    if s.startswith("apply "):
        parts = s.split()
        freq = FREQ.get(parts[1], parts[1]) if len(parts) > 1 else ""
        extra = ""
        if "prn" in parts:
            i = parts.index("prn")
            if i + 1 < len(parts):
                extra = " " + PRN.get(parts[i+1], "เมื่อมีอาการ")
        return f"ทาบริเวณที่เป็น {freq}{extra}".strip(), []

    t = s.split()
    warnings, out = [], []
    if len(t) >= 2 and re.fullmatch(r"\d+(\.\d+)?", t[0]) and t[1] in FORMS:
        out.append(f"ครั้งละ {t[0]} {FORMS[t[1]]}")
    else:
        warnings.append("รูปแบบขนาดยาไม่ตรง template เช่น 1 tab / 1 cap")

    freq_token = next((x for x in t if x in FREQ), None)
    if freq_token:
        out.append(FREQ[freq_token])
    else:
        warnings.append("ไม่พบความถี่ที่ระบบรู้จัก")

    meal_token = next((x for x in t if x in MEAL), None)
    if meal_token:
        if freq_token == "tid":
            out[-1] = "วันละ 3 ครั้ง"
            out.append(f"{MEAL[meal_token]}เช้า กลางวัน เย็น")
        elif freq_token == "bid":
            out[-1] = "วันละ 2 ครั้ง"
            out.append(f"{MEAL[meal_token]}เช้า เย็น")
        elif freq_token == "od":
            out[-1] = "วันละ 1 ครั้ง"
            out.append(f"{MEAL[meal_token]}เช้า")
        else:
            out.append(MEAL[meal_token])

    if "hs" in t and freq_token != "hs":
        out.append("ก่อนนอน")
    if "prn" in t:
        i = t.index("prn")
        if i + 1 < len(t):
            out.append(PRN.get(t[i+1], "เมื่อมีอาการ"))
        else:
            out.append("เมื่อมีอาการ")
            warnings.append("PRN ยังไม่ระบุอาการ")
    return " ".join(out), warnings

# ---------- SAFETY RULES ----------
def allergy_and_interaction_alerts(med_names, allergy_text, current_med_text):
    alerts = []
    allergy = norm_text(allergy_text)
    current = norm_text(current_med_text)
    names = [norm_text(x) for x in med_names]
    all_ordered = " | ".join(names)

    def has_any(text, words):
        return any(w in text for w in words)

    if has_any(allergy, ["penicillin","เพนิซิล","amoxicillin","ampicillin","augmentin"]):
        if any(has_any(n, ["amoxicillin","clavulanate","dicloxacillin"]) for n in names):
            alerts.append("Drug allergy alert: มีประวัติแพ้ penicillin/amoxicillin แต่มีคำสั่งยากลุ่ม penicillin")

    if has_any(allergy, ["aspirin","asa","แอสไพริน","nsaid","เอ็นเสด","ibuprofen","diclofenac","naproxen","mefenamic","celecoxib"]):
        if any(has_any(n, ["aspirin","ibuprofen","diclofenac","naproxen","mefenamic","celecoxib"]) for n in names):
            alerts.append("Drug allergy alert: มีประวัติแพ้ aspirin/NSAIDs แต่มีคำสั่งยา NSAID/aspirin")

    if has_any(allergy, ["macrolide","azithromycin","roxithromycin","erythromycin"]):
        if any(has_any(n, ["azithromycin","roxithromycin"]) for n in names):
            alerts.append("Drug allergy alert: มีประวัติแพ้ macrolide แต่มีคำสั่งยา azithromycin/roxithromycin")

    if has_any(allergy, ["quinolone","floxacin","cipro","ofloxacin","norfloxacin"]):
        if any(has_any(n, ["ciprofloxacin","ofloxacin","norfloxacin"]) for n in names):
            alerts.append("Drug allergy alert: มีประวัติแพ้ quinolone แต่มีคำสั่งยา quinolone")

    if has_any(all_ordered, ["ibuprofen","diclofenac","naproxen","mefenamic","celecoxib","aspirin"]):
        if has_any(current, ["warfarin","rivaroxaban","apixaban","dabigatran","clopidogrel","aspirin"]):
            alerts.append("Drug interaction alert: NSAID/aspirin ร่วมกับ anticoagulant/antiplatelet เพิ่มความเสี่ยงเลือดออก")
        if has_any(current, ["enalapril","losartan","acei","arb","furosemide","hctz","diuretic"]):
            alerts.append("Drug interaction alert: NSAID ร่วมกับ ACEI/ARB/diuretic อาจเพิ่มความเสี่ยงไตเสื่อม/ความดันคุมยาก")

    if "simvastatin" in current and has_any(all_ordered, ["azithromycin","roxithromycin","itraconazole"]):
        alerts.append("Drug interaction alert: simvastatin ร่วมกับ macrolide/itraconazole เพิ่มความเสี่ยง myopathy/rhabdomyolysis")

    if has_any(current, ["sertraline","fluoxetine","paroxetine","ssri","snri"]) and has_any(all_ordered, ["tramadol","dextromethorphan"]):
        alerts.append("Drug interaction alert: SSRI/SNRI ร่วมกับ tramadol/dextromethorphan เพิ่มความเสี่ยง serotonin syndrome")

    if has_any(current, ["amitriptyline","lorazepam","diazepam","alcohol","เหล้า","สุรา"]) and has_any(all_ordered, ["tramadol","hydroxyzine","cpm","chlorpheniramine","dimenhydrinate","lorazepam"]):
        alerts.append("Drug interaction alert: ยากดประสาท/แอลกอฮอล์ร่วมกับยาง่วงซึมหรือ tramadol เพิ่มความเสี่ยงง่วง ซึม หกล้ม กดหายใจ")

    if "metformin" in current and has_any(all_ordered, ["ciprofloxacin","ofloxacin","norfloxacin"]):
        alerts.append("Drug interaction alert: fluoroquinolone อาจรบกวนระดับน้ำตาลในผู้ใช้ metformin/เบาหวาน")

    return list(dict.fromkeys(alerts))

# ---------- HN HASH ----------
def normalize_hn(hn):
    return re.sub(r"[^A-Za-z0-9\-/]", "", (hn or "").strip()).upper()

def hash_hn(hn):
    if not HN_HASH_SECRET:
        raise RuntimeError("HN_HASH_SECRET is not configured")
    norm = normalize_hn(hn)
    if not norm:
        raise ValueError("HN ว่าง")
    return hmac.new(HN_HASH_SECRET.encode(), norm.encode(), hashlib.sha256).hexdigest()

def hn_fingerprint(h):
    return (h[:4] + "-" + h[4:8]).upper() if h else ""

def new_encounter_id():
    return datetime.now(BKK).strftime("%y%m%d-%H%M%S-") + secrets.token_hex(2).upper()


def get_fernet():
    if not PATIENT_DATA_KEY:
        raise RuntimeError("PATIENT_DATA_KEY is not configured")
    try:
        return Fernet(PATIENT_DATA_KEY.encode("utf-8"))
    except Exception:
        raise RuntimeError("PATIENT_DATA_KEY must be a valid Fernet key")

def encrypt_text(value):
    value = (value or "").strip()
    if not value:
        return ""
    return get_fernet().encrypt(value.encode("utf-8")).decode("utf-8")

def decrypt_text(token):
    token = (token or "").strip()
    if not token:
        return ""
    try:
        return get_fernet().decrypt(token.encode("utf-8")).decode("utf-8")
    except InvalidToken:
        return "[ถอดรหัสไม่ได้]"

def label_datetime(ts):
    try:
        dt = datetime.fromisoformat(ts)
        return f"{dt.day:02d}/{dt.month:02d}/{dt.year + 543} เวลา {dt.hour:02d}:{dt.minute:02d} น."
    except Exception:
        return ts

# ---------- GITHUB ----------
RX_FIELDS = [
    "encounter_id","timestamp_bkk","hn_hash","hn_fingerprint",
    "keyword","icd10","diagnosis","allergy","current_med",
    "first_name_enc","last_name_enc","hn_enc",
    "drug_name","sig_raw","sig_th","quantity",
    "rx_status","verified_bkk","dispensed_bkk"
]

def gh_headers():
    return {"Authorization":f"Bearer {GITHUB_TOKEN}","Accept":"application/vnd.github+json","X-GitHub-Api-Version":"2026-03-10"}

def gh_url(path):
    return f"https://api.github.com/repos/{GITHUB_OWNER}/{GITHUB_REPO}/contents/{path}"

def read_csv_from_github(path):
    if not all([GITHUB_OWNER,GITHUB_REPO,GITHUB_TOKEN]):
        raise RuntimeError("GitHub environment variables are incomplete")
    r=requests.get(gh_url(path),headers=gh_headers(),params={"ref":GITHUB_BRANCH},timeout=20)
    if r.status_code==404:return [],None
    if not r.ok:raise RuntimeError(f"GitHub read error {r.status_code}: {r.text[:300]}")
    j=r.json();content=base64.b64decode(j["content"]).decode("utf-8-sig")
    return (list(csv.DictReader(io.StringIO(content))) if content.strip() else []),j["sha"]

def put_csv_to_github(path,rows,sha,fields,message):
    sio=io.StringIO();w=csv.DictWriter(sio,fieldnames=fields);w.writeheader()
    for row in rows:w.writerow({k:row.get(k,"") for k in fields})
    body={"message":message,"content":base64.b64encode(sio.getvalue().encode()).decode(),"branch":GITHUB_BRANCH}
    if sha:body["sha"]=sha
    return requests.put(gh_url(path),headers=gh_headers(),json=body,timeout=25)

def mutate_csv_with_retry(path,fields,mutator,message,max_attempts=5):
    last=None
    for attempt in range(max_attempts):
        rows,sha=read_csv_from_github(path);rows=mutator(rows);r=put_csv_to_github(path,rows,sha,fields,message)
        if r.ok:return rows
        last=r
        if r.status_code in (409,422):
            time.sleep(.35*(attempt+1));continue
        break
    raise RuntimeError(f"GitHub save error {last.status_code if last else '?'}: {(last.text if last else '')[:300]}")

# ---------- UI ----------
BASE_HTML = """
<!doctype html><html lang="th"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{{ title }}</title>
<style>
:root{font-family:system-ui,-apple-system,"Segoe UI",sans-serif;color:#17202a}
body{margin:0;background:#f5f7fa}.wrap{max-width:1080px;margin:auto;padding:16px}
.card{background:white;border-radius:16px;padding:18px;margin:12px 0;box-shadow:0 2px 14px #00000012}
h1{font-size:1.5rem}h2{font-size:1.1rem}
button,.btn,select,input,textarea{font:inherit}
input,select,textarea{width:100%;box-sizing:border-box;padding:11px;border:1px solid #ccd3db;border-radius:10px;margin:6px 0 10px}
button,.btn{padding:11px 15px;border:0;border-radius:10px;background:#1f6feb;color:white;cursor:pointer;text-decoration:none;display:inline-block}
.secondary{background:#566573!important}.good{background:#087443!important}
.danger{color:#b42318}.ok{color:#067647}.warn{color:#b54708}.muted{color:#667085;font-size:.9rem}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:10px}.kw{background:#eef4ff;color:#1849a9}
.two{display:grid;grid-template-columns:1fr 1fr;gap:10px}.rxrow{border:1px solid #e4e7ec;border-radius:12px;padding:12px;margin:10px 0}
table{width:100%;border-collapse:collapse;font-size:.88rem}th,td{padding:8px;border-bottom:1px solid #eaecf0;text-align:left;vertical-align:top}.scroll{overflow-x:auto}
.label{border:1px solid #333;padding:10px;width:360px;background:white;color:black;margin:8px 0}
@media(max-width:700px){.two{grid-template-columns:1fr}}
</style></head><body><div class="wrap">{{ body|safe }}</div></body></html>
"""

def render_page(title,body):
    return render_template_string(BASE_HTML,title=title,body=body)

def require_role(role):
    def deco(fn):
        @wraps(fn)
        def inner(*args,**kwargs):
            if session.get("role")!=role:return redirect(url_for("login",role=role))
            return fn(*args,**kwargs)
        return inner
    return deco

@app.route("/")
def home():
    return render_page("Clinic","""
    <div class="card"><h1>Clinic ICD-10 + e-Prescribing</h1>
    <a class="btn" href="/doctor">แพทย์</a>
    <a class="btn secondary" href="/pharmacy">เภสัชกร</a></div>
    """)

@app.route("/login/<role>",methods=["GET","POST"])
def login(role):
    if role not in ("doctor","pharmacist"):return "Invalid role",400
    expected=DOCTOR_PIN if role=="doctor" else PHARMACIST_PIN
    label="แพทย์" if role=="doctor" else "เภสัชกร"
    if request.method=="POST":
        if expected and request.form.get("pin","")==expected:
            session["role"]=role
            return redirect("/doctor" if role=="doctor" else "/pharmacy")
        return render_page("Login","<div class='card'><h1>PIN ไม่ถูกต้อง</h1><a class='btn' href=''>ลองใหม่</a></div>")
    return render_page("Login",f"<div class='card'><h1>เข้าสู่ระบบ: {label}</h1><form method='post'><input name='pin' type='password' inputmode='numeric' required><button>เข้าสู่ระบบ</button></form></div>")

@app.route("/logout")
def logout():
    session.clear();return redirect("/")

@app.route("/doctor")
@require_role("doctor")
def doctor():
    buttons="".join([f"<button class='kw' type='button' onclick='chooseKeyword({json.dumps(k)})'>{k}</button>" for k in KEYWORD_HINTS])
    drug_opts="".join([f"<option value='{html.escape(x)}'>{html.escape(x)}</option>" for x in MED_OPTIONS])
    defaults=json.dumps(DEFAULT_SIG,ensure_ascii=False)
    body=f"""
<div class='card'><h1>แพทย์: HN → ICD-10 → สั่งยา</h1><div class='muted'>HN ไม่บันทึกดิบใน prescription CSV</div></div>
<div class='card'><h2>1) ข้อมูลผู้ป่วยและข้อมูล safety</h2>
<div class='two'><div><label>ชื่อ</label><input id='first_name' placeholder='ชื่อ'></div><div><label>นามสกุล</label><input id='last_name' placeholder='นามสกุล'></div></div>
<label>HN</label><input id='hn' placeholder='HN'>
<div class='two'><textarea id='allergy' placeholder='แพ้ยา (ถ้ามี)'></textarea><textarea id='current_med' placeholder='ยาประจำ/อาหารเสริม (ถ้ามี)'></textarea></div></div>
<div class='card'><h2>2) Diagnosis keyword</h2><div class='grid'>{buttons}</div><p>เลือกแล้ว: <b id='chosenKeyword'>-</b></p></div>
<div class='card'><h2>3) ICD-10</h2><input id='icdSearch' placeholder='ค้น ICD-10' oninput='searchICD()'><select id='icdSelect' size='7'></select></div>
<div class='card'><h2>4) Medication order</h2>
<div class='two'><div><label>ยา</label><select id='drugSelect'><option value=''>-- เลือกยา --</option>{drug_opts}</select></div><div><label>จำนวน</label><input id='qty' placeholder='เช่น 10'></div></div>
<label>SIG shorthand</label><input id='sigRaw' placeholder='เช่น 1 tab tid pc'>
<button type='button' class='secondary' onclick='previewSig()'>แปล SIG</button><div id='sigPreview' class='muted'></div><br>
<button type='button' onclick='addDrug()'>+ เพิ่มยา</button><div id='rxList'></div></div>
<div class='card'><h2>5) Confirm</h2><label><input id='confirm' type='checkbox' style='width:auto'> แพทย์ตรวจสอบชื่อ-นามสกุล, HN, ICD-10, allergy/current meds, รายการยา และฉลากแล้ว</label><br><br>
<button class='good' type='button' onclick='saveEncounter()'>Confirm & Send to Pharmacy</button><p id='saveStatus'></p></div>
<div class='card'><a class='btn secondary' href='/logout'>ออกจากระบบ</a></div>
<script>
const DEFAULTS={defaults};let selectedKeyword="",rxItems=[];
function chooseKeyword(k){{selectedKeyword=k;document.getElementById("chosenKeyword").textContent=k;document.getElementById("icdSearch").value="";searchICD();}}
let timer=null;
function searchICD(){{clearTimeout(timer);timer=setTimeout(async()=>{{const q=document.getElementById("icdSearch").value.trim(),s=document.getElementById("icdSelect");const r=await fetch("/api/icd-search?q="+encodeURIComponent(q)+"&keyword="+encodeURIComponent(selectedKeyword));const j=await r.json();s.innerHTML="";(j.results||[]).forEach(x=>{{const o=document.createElement("option");o.value=x.code+"||"+x.title;o.textContent=x.code+" — "+x.title;s.appendChild(o);}});}},120);}}
document.getElementById("drugSelect").addEventListener("change",()=>{{const d=document.getElementById("drugSelect").value;document.getElementById("sigRaw").value=DEFAULTS[d]||"";document.getElementById("sigPreview").textContent="";}});
async function previewSig(){{const raw=document.getElementById("sigRaw").value.trim();const r=await fetch("/api/translate-sig",{{method:"POST",headers:{{"Content-Type":"application/json"}},body:JSON.stringify({{sig_raw:raw}})}});const j=await r.json();let h="<b>ฉลาก:</b> "+(j.sig_th||"-");if(j.warnings&&j.warnings.length)h+='<div class="warn">'+j.warnings.join(" | ")+"</div>";document.getElementById("sigPreview").innerHTML=h;return j;}}
async function addDrug(){{const drug=document.getElementById("drugSelect").value,qty=document.getElementById("qty").value.trim(),raw=document.getElementById("sigRaw").value.trim();if(!drug||!qty||!raw){{alert("กรุณาเลือกยา จำนวน และ SIG");return;}}const j=await previewSig();if(!j.sig_th){{alert("SIG ยังแปลไม่ได้");return;}}rxItems.push({{drug_name:drug,quantity:qty,sig_raw:raw,sig_th:j.sig_th}});renderRx();document.getElementById("drugSelect").value="";document.getElementById("qty").value="";document.getElementById("sigRaw").value="";document.getElementById("sigPreview").textContent="";}}
function renderRx(){{const b=document.getElementById("rxList");if(!rxItems.length){{b.innerHTML='<div class="muted">ยังไม่มีรายการยา</div>';return;}}b.innerHTML=rxItems.map((x,i)=>`<div class="rxrow"><b>${{i+1}}. ${{x.drug_name}}</b> × ${{x.quantity}}<br><span class="muted">${{x.sig_raw}}</span><br>${{x.sig_th}}<br><button class="secondary" onclick="removeRx(${{i}})">ลบ</button></div>`).join("");}}
function removeRx(i){{rxItems.splice(i,1);renderRx();}}
async function saveEncounter(){{const hn=document.getElementById("hn").value.trim(),val=document.getElementById("icdSelect").value,out=document.getElementById("saveStatus");if(!hn){{out.innerHTML='<span class="danger">กรุณาระบุ HN</span>';return;}}if(!selectedKeyword||!val){{out.innerHTML='<span class="danger">กรุณาเลือก ICD-10</span>';return;}}if(!rxItems.length){{out.innerHTML='<span class="danger">กรุณาเพิ่มยา</span>';return;}}if(!document.getElementById("confirm").checked){{out.innerHTML='<span class="danger">กรุณา Confirm</span>';return;}}const [icd10,diagnosis]=val.split("||");const payload={{hn,keyword:selectedKeyword,icd10,diagnosis,allergy:document.getElementById("allergy").value,current_med:document.getElementById("current_med").value,rx_items:rxItems}};const r=await fetch("/api/save-encounter",{{method:"POST",headers:{{"Content-Type":"application/json"}},body:JSON.stringify(payload)}});const j=await r.json();if(!r.ok){{out.innerHTML='<span class="danger">'+(j.error||"Save failed")+'</span>';return;}}out.innerHTML='<span class="ok">บันทึกแล้ว '+j.encounter_id+'</span>';rxItems=[];renderRx();document.getElementById("confirm").checked=false;}}
renderRx();
</script>
"""
    return render_page("Doctor",body)

@app.get("/api/icd-search")
@require_role("doctor")
def api_icd_search():
    q=request.args.get("q","");keyword=request.args.get("keyword","")
    if not q and keyword not in KEYWORD_HINTS:return jsonify(results=[])
    return jsonify(results=icd_search(q=q,hint=keyword,limit=50))

@app.post("/api/translate-sig")
@require_role("doctor")
def api_translate_sig():
    j=request.get_json(force=True);sig_th,warnings=translate_sig(j.get("sig_raw",""))
    return jsonify(sig_th=sig_th,warnings=warnings)

@app.post("/api/save-encounter")
@require_role("doctor")
def save_encounter():
    j=request.get_json(force=True)
    first_name=(j.get("first_name") or "").strip();last_name=(j.get("last_name") or "").strip();hn=normalize_hn(j.get("hn",""));kw=j.get("keyword","");icd10=(j.get("icd10") or "").strip().upper()
    allergy=(j.get("allergy") or "").strip();current_med=(j.get("current_med") or "").strip();rx_items=j.get("rx_items") or []
    if not first_name or not last_name:return jsonify(error="กรุณาระบุชื่อและนามสกุล"),400
    if not hn:return jsonify(error="HN ว่าง"),400
    if kw not in KEYWORD_HINTS:return jsonify(error="Keyword ไม่ถูกต้อง"),400
    item=icd_lookup_exact(icd10)
    if not item:return jsonify(error="ไม่พบ ICD-10 นี้ใน dictionary"),400
    if not rx_items:return jsonify(error="ไม่มีรายการยา"),400
    try:h=hash_hn(hn)
    except Exception as e:return jsonify(error=str(e)),500

    enc=new_encounter_id();ts=datetime.now(BKK).isoformat(timespec="seconds");clean=[];med_names=[]
    try:
        first_name_enc=encrypt_text(first_name);last_name_enc=encrypt_text(last_name);hn_enc=encrypt_text(hn)
    except Exception as e:
        return jsonify(error=str(e)),500
    for rx in rx_items:
        drug=find_med_in_stock(rx.get("drug_name",""))
        if not drug:return jsonify(error=f"ไม่พบยาใน stock: {rx.get('drug_name','')}"),400
        sig_raw=(rx.get("sig_raw") or "").strip();sig_th,_=translate_sig(sig_raw);qty=re.sub(r"[^0-9.]", "", str(rx.get("quantity","")))
        if not sig_th or not qty:return jsonify(error=f"ข้อมูลยาไม่ครบ: {drug}"),400
        med_names.append(drug)
        clean.append({"encounter_id":enc,"timestamp_bkk":ts,"hn_hash":h,"hn_fingerprint":hn_fingerprint(h),"keyword":kw,"icd10":icd10,"diagnosis":item["title"],"allergy":allergy,"current_med":current_med,"first_name_enc":first_name_enc,"last_name_enc":last_name_enc,"hn_enc":hn_enc,"drug_name":drug,"sig_raw":sig_raw,"sig_th":sig_th,"quantity":qty,"rx_status":"รอจัดยา","verified_bkk":"","dispensed_bkk":""})

    def add_rows(rows):return rows+clean
    try:mutate_csv_with_retry(GITHUB_RX_CSV_PATH,RX_FIELDS,add_rows,f"Add prescription {enc} {ts}")
    except Exception as e:return jsonify(error=str(e)),500
    return jsonify(ok=True,encounter_id=enc,timestamp_bkk=ts,alerts=allergy_and_interaction_alerts(med_names,allergy,current_med))

def get_today_queue(all_rows):
    today=datetime.now(BKK).date();result=[]
    for r in all_rows:
        try:dt=datetime.fromisoformat(r.get("timestamp_bkk",""))
        except Exception:continue
        if dt.date()==today and r.get("rx_status")!="จ่ายยาแล้ว":result.append(r)
    return result

@app.route("/pharmacy")
@require_role("pharmacist")
def pharmacy():
    q=request.args.get("hn","").strip();err="";rows=[]
    try:
        all_rows,_=read_csv_from_github(GITHUB_RX_CSV_PATH)
        rows=[r for r in all_rows if r.get("hn_hash")==hash_hn(q)] if q else get_today_queue(all_rows)
    except Exception as e:err=str(e)

    groups={}
    for r in rows:groups.setdefault(r.get("encounter_id",""),[]).append(r)

    cards=[]
    for enc,items in sorted(groups.items(),key=lambda kv:kv[1][0].get("timestamp_bkk",""),reverse=True):
        first=items[0];med_names=[x.get("drug_name","") for x in items]
        try:
            patient_first=decrypt_text(first.get("first_name_enc",""))
            patient_last=decrypt_text(first.get("last_name_enc",""))
            patient_hn=decrypt_text(first.get("hn_enc",""))
        except Exception:
            patient_first=patient_last=patient_hn="[ถอดรหัสไม่ได้]"
        alerts=allergy_and_interaction_alerts(med_names,first.get("allergy",""),first.get("current_med",""))
        alert_html="".join([f"<div class='danger'><b>⚠ {html.escape(a)}</b></div>" for a in alerts])
        if first.get("allergy","").strip():alert_html+=f"<div class='warn'><b>แพ้ยา:</b> {html.escape(first.get('allergy',''))}</div>"
        if first.get("current_med","").strip():alert_html+=f"<div class='muted'><b>ยาประจำ:</b> {html.escape(first.get('current_med',''))}</div>"

        rows_html="";labels_html=""
        for i,x in enumerate(items,1):
            rows_html+=f"<tr><td>{html.escape(x.get('drug_name',''))}</td><td>{html.escape(x.get('sig_raw',''))}</td><td>{html.escape(x.get('sig_th',''))}</td><td>{html.escape(x.get('quantity',''))}</td></tr>"
            label=f"สถานพยาบาล มก. กำแพงแสน\\nชื่อ: {patient_first} {patient_last}\\nHN: {patient_hn}\\nวันที่สั่งยา: {label_datetime(first.get('timestamp_bkk',''))}\\nยา: {x.get('drug_name','')}\\nจำนวน: {x.get('quantity','')}\\nวิธีใช้: {x.get('sig_th','')}"
            safe=html.escape(label).replace("\\n","<br>");uid=str(uuid.uuid4()).replace("-","")
            labels_html+=f"""<details><summary>ป้ายยา {i}: {html.escape(x.get('drug_name',''))}</summary>
<div id='label_{uid}' class='label'>{safe}</div>
<button type='button' onclick='printLabel_{uid}()'>พิมพ์ป้ายยานี้</button>
<script>function printLabel_{uid}(){{var contents=document.getElementById('label_{uid}').innerHTML;var w=window.open('','','height=500,width=420');w.document.write('<html><head><title>Drug label</title><style>@media print{{@page{{size:80mm auto;margin:5mm}}body{{font-family:Arial,sans-serif;font-size:14px}}}}</style></head><body>'+contents+'</body></html>');w.document.close();w.focus();setTimeout(function(){{w.print();w.close();}},300);}}</script></details>"""

        status=first.get("rx_status","รอจัดยา")
        if status=="รอจัดยา":
            action=f"<form method='post' action='/pharmacy/status/{enc}'><input type='hidden' name='status' value='จัดยาแล้ว'><button class='good'>จัดยาแล้ว</button></form>"
        elif status=="จัดยาแล้ว":
            action=f"<form method='post' action='/pharmacy/status/{enc}'><input type='hidden' name='status' value='จ่ายยาแล้ว'><button class='good'>จ่ายยาแล้ว</button></form>"
        else:
            action="<span class='ok'><b>จ่ายยาแล้ว</b></span>"

        cards.append(f"""<div class='card'><h2>{first.get('timestamp_bkk','')} | HN {first.get('hn_fingerprint','')} | {status}</h2>
<div><b>{first.get('icd10','')}</b> — {html.escape(first.get('diagnosis',''))}</div><div class='muted'><b>ผู้ป่วย:</b> {html.escape(patient_first)} {html.escape(patient_last)} | <b>HN:</b> {html.escape(patient_hn)}</div>{alert_html}
<div class='scroll'><table><thead><tr><th>ยา</th><th>SIG แพทย์</th><th>ฉลากไทย</th><th>จำนวน</th></tr></thead><tbody>{rows_html}</tbody></table></div>
<h3>ป้ายยา</h3>{labels_html}
<p class='warn'><b>หากไม่เห็นด้วยกับคำสั่งยา กรุณาเดินมาปรึกษาแพทย์โดยตรง</b><br>ไม่มีการ Reject/Send back/แก้คำสั่งแพทย์ผ่านระบบ</p>{action}</div>""")

    body=f"""<div class='card'><h1>Pharmacy Dashboard</h1><form method='get'><label>ค้นหาด้วย HN จากเวชระเบียน</label><input name='hn' value='{html.escape(q)}' placeholder='HN'><button>ค้นหา</button> <a class='btn secondary' href='/pharmacy'>คิววันนี้</a></form>
<div class='muted'>Dashboard แสดง hashed HN fingerprint; raw HN ไม่บันทึกใน prescription CSV</div>{f"<p class='danger'>{html.escape(err)}</p>" if err else ""}</div>
{''.join(cards) if cards else "<div class='card muted'>ยังไม่พบรายการ</div>"}<div class='card'><a class='btn secondary' href='/logout'>ออกจากระบบ</a></div>"""
    return render_page("Pharmacy",body)

@app.post("/pharmacy/status/<encounter_id>")
@require_role("pharmacist")
def pharmacy_status(encounter_id):
    new_status=request.form.get("status","")
    if new_status not in ("จัดยาแล้ว","จ่ายยาแล้ว"):return "Invalid status",400
    now=datetime.now(BKK).isoformat(timespec="seconds")
    def mutate(rows):
        found=False
        for r in rows:
            if r.get("encounter_id")==encounter_id:
                found=True;r["rx_status"]=new_status
                if new_status=="จัดยาแล้ว":r["verified_bkk"]=now
                if new_status=="จ่ายยาแล้ว":
                    if not r.get("verified_bkk"):r["verified_bkk"]=now
                    r["dispensed_bkk"]=now
        if not found:raise ValueError("ไม่พบ encounter")
        return rows
    mutate_csv_with_retry(GITHUB_RX_CSV_PATH,RX_FIELDS,mutate,f"Update prescription {encounter_id} -> {new_status}")
    return redirect("/pharmacy")

@app.get("/health")
def health():
    return jsonify(ok=True,time=datetime.now(BKK).isoformat())

if __name__=="__main__":
    app.run(debug=True)
