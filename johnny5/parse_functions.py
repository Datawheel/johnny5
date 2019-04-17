try:
    xrange
except NameError:
    xrange = range

import mwparserfromhell,re

def drop_comments(value):
	'''Drops wikimarkup comments from the provided string.'''
	while '<!--' in value:
		comment = value[value.find('<!--'):].split('-->')[0]+'-->'
		value = value.replace(comment,'')
	return value

def drop_nowrap(text):
    '''Drops nowrap'''
    text = re.sub(r'\{\{[^\|]*[Nn]owrap[^\|]*\|','{{nowrap|',text)
    nowrap = ''
    p_count = 0
    if '{{nowrap|' in text:
        for c in text[text.lower().find('{{nowrap|'):]:
            nowrap += c
            if c == '{':
                p_count +=1
            if c == '}':
                p_count +=-1
            if p_count ==0:
                break
        text = text.replace(nowrap,nowrap[9:-2])
    return text

def get_links(text):
    '''
    Gets the links from the provided in Wiki Markup.
    Links are between square brackets [[]].
    '''
    links = []
    while '[[' in text:
        link = text[text.find('[[')+2:].split(']]')[0]
        text = text.replace('[['+link+']]','')
        if '|' in link:
            link = link.split('|')[0].strip()
        links.append(link.strip())
    return links

def find_nth(haystack, needle, n):
	'''Returns the index of the nth occurrence of needle in haystack.

	Parameters
	----------
	haystack : str
		String to search.
	needle : str
		Pattern to find.
	n : int
		Occurrence to return.
	'''
	start = haystack.find(needle)
	while start >= 0 and n > 1:
		start = haystack.find(needle, start+len(needle))
		n -= 1
	return start

def first_month(pt,as_num=False):
    '''Returns the first month in the string. Returns 'NA' when there is no month. '''
    pt_ = pt.lower()
    months = ['january','february','march','april','may','june','july','august','september','october','november','december']
    mm = 'NA'
    i = 10000
    for month in months:
        if month in pt_:
            if pt_.find(month) < i:
                i = pt_.find(month)
                mm = month
    if mm =="NA":
        months = ['jan','feb','mar','apr','may','jun','jul','aug','sep','oct','nov','dec']
        for month in months:
            if month in pt_:
                if pt_.find(month) < i:
                    i = pt_.find(month)
                    mm = month
    if as_num:
        mp = dict(zip(months,range(1,13)))
        return mp[mm]
    else:
        return mm

def parse_ints(s):
    '''Parses a list of integers from s'''
    items = []
    item = ''
    for c in s:
        try:
            c = unicode(int(c))
            item += c
        except:
            if len(item) !=0:
                items.append(int(item))
                item = ''
    if len(item) !=0:
        items.append(int(item))
        item = ''
    #if len(items) == 0:
        #items.append('NA')
    return items

def has_num(text):
    '''Returns True if there is a number in the text.'''
    for c in text:
        try:
            c = int(c)
            return True
        except:
            pass
    return False

def parse_date(t):
    """Parses a date from the given string.
    This function is constantly under development since new date formats are added to wikipedia every day.
    The current version is optimized for parsing death dates.
    """
    t = drop_nowrap(t)
    t = re.sub(r'\{\{[^\|]*[Cc]irca[^\}]*\}\}','',t).strip()

    template = mwparserfromhell.parse(t).filter_templates()
    yy, mm, dd = 'NA', 'NA', 'NA'

    if len(template) != 0:
        template = template[0]
        tag = re.sub(r'_+','_',template.name.lower().strip().replace(' ', '_'))

        if tag in set(['birth_date', 'death_date_and_age', 'birth_date_and_age', 'death_date', 'dda', 'age_in_years_and_days', 'death_date_and_given_age']):
            ii = -1
            while yy == 'NA':
                ii += 1
                try:
                    yy = int(template.params[ii].value.strip())
                except:
                    if ii>len(template.params):
                        break
            while mm == 'NA':
                ii += 1
                try:
                    mm = int(template.params[ii].value.strip())
                except:
                    if ii>len(template.params):
                        break
            while dd == 'NA':
                ii += 1
                try:
                    dd = int(template.params[ii].value.strip())
                except:
                    if ii>len(template.params):
                        break
        elif tag in set(['death_year_and_age']):
            yy = template.params[0]
            if len(template.params) > 2:
                mm = template.params[2]
        elif tag in set(['oldstyledate']):
            yy = int(template.params[1].value.strip())
            dd = parse_ints(template.params[0].value.strip())[0]
            mm = first_month(template.params[0].value.strip(),as_num=True)
        elif tag in set(['birth-date','death-date_and_age','death-date','d-da']):
            ii = 0
            while True:
                try:
                    val = template.params[ii].value.strip()
                    nums = parse_ints(val)
                    if len(nums) !=0:
                        break
                    else:
                        ii+=1
                except:
                    ii+=1
                if ii>len(template.params):
                    break
            if len(nums) !=0:
                dd = nums[0]
                yy = nums[1]
                mm = first_month(val,as_num=True)
        elif tag in set(['birthdeathage']):
            ii = len(template.params)
            while dd == 'NA':
                ii-=1
                try:
                    dd = int(template.params[ii].value.strip())
                except:
                    if ii<0:
                        break
            while mm == 'NA':
                ii-=1
                try:
                    mm = int(template.params[ii].value.strip())
                except:
                    if ii>0:
                        break
            while yy == 'NA':
                ii-=1
                try:
                    yy = int(template.params[ii].value.strip())
                except:
                    if ii>0:
                        break
        elif tag in set(['cite_news','cite_web','refn']):
            pass
        else:
            raise NameError('Unrecognized tag '+tag)

    return str(yy), str(mm), str(dd)


def permute(title):
    '''Creates all combinations of upper and lower cases in the title'''
    start = [0]+[i+1 for i,char in enumerate(title) if char == ' ']
    titles = []
    n = 2**len(start)
    if n < 100:
        combinations= [('0'*len(start)+bin(i).split('b')[-1])[-len(start):] for i in xrange(n)]
        for c in combinations:
            tt = ''
            for i,val in enumerate(c):
                if val =='0':
                    tt += title[start[i]].lower()+title[start[i]+1:].split(' ')[0]+' '
                elif val == '1':
                    tt += title[start[i]].upper()+title[start[i]+1:].split(' ')[0]+' '
            titles.append(tt)
    return titles[::-1]

def correct_titles(title):
    '''Checks the capitalization of the given title and returns a set of possible uses'''
    titles = set([title])
    title = title.lower()
    bag = set(['a','an','the','for','and','nor','but','or','yet','so','at','around','by','after','along','for','from','of','on','to','with','without'])
    words = title.split(' ')
    words[0] = words[0][0].upper()+words[0][1:]
    titles.add(str.join(' ', words))
    #titles.add(' '.join(words))
    words[-1] = words[-1][0].upper()+words[-1][1:]
    titles.add(str.join(' ', words))
    #titles.add(' '.join(words))
    for i,word in enumerate(words):
        if i!=0:
            if word not in bag:
                words[i] = words[i][0].upper()+words[i][1:]
    titles.add(str.join(' ', words))
    #titles.add(' '.join(words))
    words[-1] = words[-1][0].upper()+words[-1][1:]
    titles.add(str.join(' ', words))
    #titles.add(' '.join(words))
    return list(titles)

def parse_p(s, sep='()'):
	'''
	Parses parenthesis from a string.

	Returns
	-------
	ps : list
		List of parenthesis
	'''
	sep0,sep1 = sep
	ps = []
	p = ''
	stack = 0
	for i in s:
		if i == sep0:
			stack+=1
		if stack>0:
			p+=i
		if i == sep1:
			stack-=1
		if (stack == 0)&(p!=''):
			ps.append(p)
			p = ''
	return ps